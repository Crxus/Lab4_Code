#include <proc.h>
#include <kmalloc.h>
#include <string.h>
#include <sync.h>
#include <pmm.h>
#include <error.h>
#include <sched.h>
#include <elf.h>
#include <vmm.h>
#include <trap.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/* ------------- process/thread mechanism design&implementation -------------
(an simplified Linux process/thread mechanism )
introduction:
  ucore implements a simple process/thread mechanism. process contains the independent memory sapce, at least one threads
for execution, the kernel data(for management), processor state (for context switch), files(in lab6), etc. ucore needs to
manage all these details efficiently. In ucore, a thread is just a special kind of process(share process's memory).
------------------------------
process state       :     meaning               -- reason
    PROC_UNINIT     :   uninitialized           -- alloc_proc
    PROC_SLEEPING   :   sleeping                -- try_free_pages, do_wait, do_sleep
    PROC_RUNNABLE   :   runnable(maybe running) -- proc_init, wakeup_proc, 
    PROC_ZOMBIE     :   almost dead             -- do_exit

-----------------------------
process state changing:
                                            
  alloc_proc                                 RUNNING
      +                                   +--<----<--+
      +                                   + proc_run +
      V                                   +-->---->--+ 
PROC_UNINIT -- proc_init/wakeup_proc --> PROC_RUNNABLE -- try_free_pages/do_wait/do_sleep --> PROC_SLEEPING --
                                           A      +                                                           +
                                           |      +--- do_exit --> PROC_ZOMBIE                                +
                                           +                                                                  + 
                                           -----------------------wakeup_proc----------------------------------
-----------------------------
process relations
parent:           proc->parent  (proc is children)
children:         proc->cptr    (proc is parent)
older sibling:    proc->optr    (proc is younger sibling)
younger sibling:  proc->yptr    (proc is older sibling)
-----------------------------
related syscall for process:
SYS_exit        : process exit,                           -->do_exit
SYS_fork        : create child process, dup mm            -->do_fork-->wakeup_proc
SYS_wait        : wait process                            -->do_wait
SYS_exec        : after fork, process execute a program   -->load a program and refresh the mm
SYS_clone       : create child thread                     -->do_fork-->wakeup_proc
SYS_yield       : process flag itself need resecheduling, -- proc->need_sched=1, then scheduler will rescheule this process
SYS_sleep       : process sleep                           -->do_sleep 
SYS_kill        : kill process                            -->do_kill-->proc->flags |= PF_EXITING
                                                                 -->wakeup_proc-->do_wait-->do_exit   
SYS_getpid      : get the process's pid

*/

// the process set's list
list_entry_t proc_list;

#define HASH_SHIFT          10
#define HASH_LIST_SIZE      (1 << HASH_SHIFT)//1024
#define pid_hashfn(x)       (hash32(x, HASH_SHIFT))

/*
#include <stdlib.h>

/* 2^31 + 2^29 - 2^25 + 2^22 - 2^19 - 2^16 + 1 
#define GOLDEN_RATIO_PRIME_32       0x9e370001UL


 * hash32 - generate a hash value in the range [0, 2^@bits - 1]
 * @val:    the input value
 * @bits:   the number of bits in a return value
 *
 * High bits are more random, so we use them.

uint32_t
hash32(uint32_t val, unsigned int bits) {
    uint32_t hash = val * GOLDEN_RATIO_PRIME_32;
    return (hash >> (32 - bits));
}

*/

// has list for process set based on pid
static list_entry_t hash_list[HASH_LIST_SIZE];

// idle proc
struct proc_struct *idleproc = NULL;
// init proc
struct proc_struct *initproc = NULL;
// current proc
struct proc_struct *current = NULL; //running process

static int nr_process = 0;

void kernel_thread_entry(void);
void forkrets(struct trapframe *tf);
void switch_to(struct context *from, struct context *to);

// alloc_proc - alloc a proc_struct and init all fields of proc_struct
static struct proc_struct *
alloc_proc(void) {
    struct proc_struct *proc = kmalloc(sizeof(struct proc_struct));
    if (proc != NULL) {
        proc->state=PROC_UNINIT; //it has just been created, and hasn't been initialized
        proc->pid=-1; //same as state
        proc->cr3=boot_cr3; //that means now it use the kernel page dictionary
        proc->need_resched=0; //this member means it should be schduled
        proc->parent=NULL; //doesn't have parent
        proc->mm=NULL; //we are not about to use mm in this lab
        proc->runs=0;  //just has been initialized
        proc->flags=0;  //same as runs
        proc->kstack=0; //same as runs, and according to the gitbook of TsingHua
        proc->tf=NULL;  //
        memset(proc->name,0,PROC_NAME_LEN+1);
        memset(&(proc->context),0,sizeof(struct context));
    //LAB4:EXERCISE1 YOUR CODE
    /*
     * below fields in proc_struct need to be initialized
     *   d    enum proc_state state;                      // Process state
     *    d   int pid;                                    // Process ID
     *    d   int runs;                                   // the running times of Proces
     *    d   uintptr_t kstack;                           // Process kernel stack
     *    d   volatile bool need_resched;                 // bool value: need to be rescheduled to release CPU?
     *      d struct proc_struct *parent;                 // the parent process
     *      d struct mm_struct *mm;                       // Process's memory management field
     *     d  struct context context;                     // Switch here to run process
     *      d struct trapframe *tf;                       // Trap frame for current interrupt
     *    d   uintptr_t cr3;                              // CR3 register: the base addr of Page Directroy Table(PDT)
     *      d uint32_t flags;                             // Process flag
     *     d  char name[PROC_NAME_LEN + 1];               // Process name
     */
    }
    return proc;
}
//**ATTENTION!!**
//memset  to clear a array or a structure or a class (*buffer,value, length)  

// set_proc_name - set the name of proc
char *
set_proc_name(struct proc_struct *proc, const char *name) {
    memset(proc->name, 0, sizeof(proc->name));
    return memcpy(proc->name, name, PROC_NAME_LEN);
}

// get_proc_name - get the name of proc
char *
get_proc_name(struct proc_struct *proc) {
    static char name[PROC_NAME_LEN + 1];
    memset(name, 0, sizeof(name));
    return memcpy(name, proc->name, PROC_NAME_LEN);
}//and return the name

// get_pid - alloc a unique pid for process
static int
get_pid(void) {
    static_assert(MAX_PID > MAX_PROCESS);
    struct proc_struct *proc;
    list_entry_t *list = &proc_list, *le;
    static int next_safe = MAX_PID, last_pid = MAX_PID;
    if (++ last_pid >= MAX_PID) {
        last_pid = 1;
        goto inside;
    }
    if (last_pid >= next_safe) {
    inside:
        next_safe = MAX_PID;
    repeat:
        le = list;
        while ((le = list_next(le)) != list) {
            proc = le2proc(le, list_link);    //just like le2page in lab2 and lab3, we use the pointer sub the offset of member to get the structure
            if (proc->pid == last_pid) {
                if (++ last_pid >= next_safe) {
                    if (last_pid >= MAX_PID) {
                        last_pid = 1;
                    }
                    next_safe = MAX_PID;
                    goto repeat;
                }
            }
            else if (proc->pid > last_pid && next_safe > proc->pid) {
                next_safe = proc->pid;
            }
        }
    }
    return last_pid;
}

/*   **ATTENTION**
 How does get_pid do?
 next_safe and last_pid are static ,and was inititalized to MAX_PID(2*MAX_PROCESS);
 then we set last_pid to 1 (means we will check the id from 1 to MAX_PID
 then check the process list, if proc->pid==last_pid (means we can't use this process id), plus the last_pid by 1
 if last_pid==MAX_PID, means we have already check the list for one turn, then set it to 1, restart the check
 then finally we have got a unused id (last_pid), to the else part.
 If proc->pid>last_pid(definetly) and naxt_safe>proc->pid, we set next_safe=proc->pid
 in the last, the area (next_safe,MAX_PID) are all useable
 return last_pid.
*/


// proc_run - make process "proc" running on cpu
// NOTE: before call switch_to, should load  base addr of "proc"'s new PDT
void
proc_run(struct proc_struct *proc) {
    if (proc != current) {
        bool intr_flag;
        struct proc_struct *prev = current, *next = proc;
        local_intr_save(intr_flag);   //if the FL_IF (the controling bit for interruption of a process) is 1(means the process can be interrupted)
        // unable the interruption, and return a 1(now intr_flag=1), 
        {
            current = proc;
            load_esp0(next->kstack + KSTACKSIZE);
            lcr3(next->cr3);//to set the environment for the new process
            switch_to(&(prev->context), &(next->context));
        }
        local_intr_restore(intr_flag);   //if intr_flag=1, enable the interruption
    }
//shut down the intrruption, so that there is no another process during we are changing the current process.

}

// forkret -- the first kernel entry point of a new thread/process
// NOTE: the addr of forkret is setted in copy_thread function
//       after switch_to, the current proc will execute here.
static void
forkret(void) {
    forkrets(current->tf);
} //WATCH MORE!!!!

// hash_proc - add proc into proc hash_list
static void
hash_proc(struct proc_struct *proc) {
    list_add(hash_list + pid_hashfn(proc->pid), &(proc->hash_link));  //pid_hashfn the hash function
}

// find_proc - find proc frome proc hash_list according to pid
struct proc_struct *
find_proc(int pid) {
    if (0 < pid && pid < MAX_PID) {
        list_entry_t *list = hash_list + pid_hashfn(pid), *le = list;  //hash_list+pid_hashfn try to find the process quicker(there is a possiblity
        //A list-hashmap
        while ((le = list_next(le)) != list) {
            struct proc_struct *proc = le2proc(le, hash_link);
            if (proc->pid == pid) {
                return proc;
            }
        }
    }
    return NULL;
}

// kernel_thread - create a kernel thread using "fn" function
// NOTE: the contents of temp trapframe tf will be copied to 
//       proc->tf in do_fork-->copy_thread function
int
kernel_thread(int (*fn)(void *), void *arg, uint32_t clone_flags) {   //fn is a function pointer and arg is the context 
    struct trapframe tf;
    memset(&tf, 0, sizeof(struct trapframe));
    tf.tf_cs = KERNEL_CS;   //code segment of kernel
    tf.tf_ds = tf.tf_es = tf.tf_ss = KERNEL_DS;  //data segment of kernel
    tf.tf_regs.reg_ebx = (uint32_t)fn;   //the function to be 
    tf.tf_regs.reg_edx = (uint32_t)arg;   //arg of the func
    tf.tf_eip = (uint32_t)kernel_thread_entry;  //to be returned??
/* 
kernel_thread_entry:        # void kernel_thread(void)

    pushl %edx              # push arg
    call *%ebx              # call fn

    pushl %eax              # save the return value of fn(arg)
    call do_exit            # call do_exit to terminate current thread
    eip is the return of the function
*/

    return do_fork(clone_flags | CLONE_VM, 0, &tf);
    //to be written
    //#define CLONE_VM            0x00000100  // set if VM shared between processes
    //#define CLONE_THREAD        0x00000200  // thread group
}

// setup_kstack - alloc pages with size KSTACKPAGE as process kernel stack
static int
setup_kstack(struct proc_struct *proc) {
    struct Page *page = alloc_pages(KSTACKPAGE);   //KSTACKPAGE=2
    if (page != NULL) {  
        proc->kstack = (uintptr_t)page2kva(page);  //page2kva to get the kerneladdress(vitual address) of page
        return 0;
    }
    return -E_NO_MEM;
}

// put_kstack - free the memory space of process kernel stack
static void
put_kstack(struct proc_struct *proc) {
    free_pages(kva2page((void *)(proc->kstack)), KSTACKPAGE);
}    //clear the space  (that we can apply new space for the stack?  
//or clear the stack

// copy_mm - process "proc" duplicate OR share process "current"'s mm according clone_flags
//         - if clone_flags & CLONE_VM, then "share" ; else "duplicate"
static int
copy_mm(uint32_t clone_flags, struct proc_struct *proc) {
    assert(current->mm == NULL);
    /* do nothing in this project */
    return 0;
}

// copy_thread - setup the trapframe on the  process's kernel stack top and
//             - setup the kernel entry point and stack of process
static void
copy_thread(struct proc_struct *proc, uintptr_t esp, struct trapframe *tf) {
    proc->tf = (struct trapframe *)(proc->kstack + KSTACKSIZE) - 1;  //setup a new space on the top of the proc->kstack
    *(proc->tf) = *tf;
    proc->tf->tf_regs.reg_eax = 0;  //returning value (of do fork???)
    proc->tf->tf_esp = esp;  //set the stack pointer(top of the stack)
    proc->tf->tf_eflags |= FL_IF;  //interrupt  could respond/respondable

    proc->context.eip = (uintptr_t)forkret;   //the next command when intrrupt happens, the we jump back and execute this function
    proc->context.esp = (uintptr_t)(proc->tf);  //the stack ...  esp is tf!!
    
}

/* do_fork -     parent process for a new child process
 * @clone_flags: used to guide how to clone the child process
 * @stack:       the parent's user stack pointer. if stack==0, It means to fork a kernel thread.
 * @tf:          the trapframe info, which will be copied to child process's proc->tf
 */
int
do_fork(uint32_t clone_flags, uintptr_t stack, struct trapframe *tf) {
    int ret = -E_NO_FREE_PROC;
    struct proc_struct *proc;
    if (nr_process >= MAX_PROCESS) {
        goto fork_out;
    }
    ret = -E_NO_MEM;
    //**ATTENTION!!!!!!**
    // it is current who called this function to create the child process
    //parents!!1
    proc=alloc_proc();
    if(proc==NULL)
    {
        goto fork_out;
    }

    proc->parent=current;
    proc=alloc_proc();
    
    if(setup_kstack(proc)!=0)  //no enough space to set a kstack-->clean a new space
    {
        goto bad_fork_cleanup_kstack;
    }
    if(copy_mm(clone_flags,proc)!=0)
    {
        goto bad_fork_cleanup_kstack;
    }
    copy_thread(proc,stack,tf); //set the stack and tf and context of proc??
    
    //In my own understanding: add the process to the hash list and the list cannot be interrupted, we can't add different process to the lists
    //so turn off the interruption
    bool intr_flag;
    local_intr_save(intr_flag); 
    {
        proc->pid=get_pid(); //get a id for this process
        list_add(&proc_list,&proc->list_link);
        hash_proc(proc);
        nr_process+=1;
    }
    local_intr_restore(intr_flag); 
    wakeup_proc(proc);
    ret=proc->pid;
    //LAB4:EXERCISE2 YOUR CODE
    /*
     * Some Useful MACROs, Functions and DEFINEs, you can use them in below implementation.
     * MACROs or Functions:
     *   alloc_proc:   create a proc struct and init fields (lab4:exercise1)
     *   setup_kstack: alloc pages with size KSTACKPAGE as process kernel stack
     *   copy_mm:      process "proc" duplicate OR share process "current"'s mm according clone_flags
     *                 if clone_flags & CLONE_VM, then "share" ; else "duplicate"
     *   copy_thread:  setup the trapframe on the  process's kernel stack top and
     *                 setup the kernel entry point and stack of process
     *   hash_proc:    add proc into proc hash_list
     *   get_pid:      alloc a unique pid for process
     *   wakeup_proc:  set proc->state = PROC_RUNNABLE
     * VARIABLES:
     *   proc_list:    the process set's list
     *   nr_process:   the number of process set
     */

    //    1. call alloc_proc to allocate a proc_struct
    //    2. call setup_kstack to allocate a kernel stack for child process
    //    3. call copy_mm to dup OR share mm according clone_flag
    //    4. call copy_thread to setup tf & context in proc_struct
    //    5. insert proc_struct into hash_list && proc_list
    //    6. call wakeup_proc to make the new child process RUNNABLE
    //    7. set ret vaule using child proc's pid
fork_out:
    return ret;

bad_fork_cleanup_kstack:
    put_kstack(proc);    //
bad_fork_cleanup_proc:
    kfree(proc);
    goto fork_out;
}

// do_exit - called by sys_exit
//   1. call exit_mmap & put_pgdir & mm_destroy to free the almost all memory space of process
//   2. set process' state as PROC_ZOMBIE, then call wakeup_proc(parent) to ask parent reclaim itself.
//   3. call scheduler to switch to other process
int
do_exit(int error_code) {
    panic("process exit!!.\n");
}

// init_main - the second kernel thread used to create user_main kernel threads
static int
init_main(void *arg) {
    cprintf("this initproc, pid = %d, name = \"%s\"\n", current->pid, get_proc_name(current));
    cprintf("To U: \"%s\".\n", (const char *)arg);
    cprintf("To U: \"en.., Bye, Bye. :)\"\n");
    return 0;
}

// proc_init - set up the first kernel thread idleproc "idle" by itself and 
//           - create the second kernel thread init_main
void
proc_init(void) {
    int i;

    list_init(&proc_list);
    for (i = 0; i < HASH_LIST_SIZE; i ++) {
        list_init(hash_list + i);
    }

    if ((idleproc = alloc_proc()) == NULL) {
        panic("cannot alloc idleproc.\n");
    }

    idleproc->pid = 0;
    idleproc->state = PROC_RUNNABLE;
    idleproc->kstack = (uintptr_t)bootstack;
    idleproc->need_resched = 1;
    set_proc_name(idleproc, "idle");
    nr_process ++;

    current = idleproc;

    int pid = kernel_thread(init_main, "Hello world!!", 0);
    if (pid <= 0) {
        panic("create init_main failed.\n");
    }

    initproc = find_proc(pid);
    set_proc_name(initproc, "init");

    assert(idleproc != NULL && idleproc->pid == 0);
    assert(initproc != NULL && initproc->pid == 1);
}

// cpu_idle - at the end of kern_init, the first kernel thread idleproc will do below works
void
cpu_idle(void) {
    while (1) {
        if (current->need_resched) {
            schedule();
        }
    }
}

/*
** ATTENTION!!**

switch_to:                      # switch_to(from, to)

    # save from's registers
    movl 4(%esp), %eax          # eax points to from
    popl 0(%eax)                # save eip !popl
    movl %esp, 4(%eax)          # save esp::context of from
    movl %ebx, 8(%eax)          # save ebx::context of from
    movl %ecx, 12(%eax)         # save ecx::context of from
    movl %edx, 16(%eax)         # save edx::context of from
    movl %esi, 20(%eax)         # save esi::context of from
    movl %edi, 24(%eax)         # save edi::context of from
    movl %ebp, 28(%eax)         # save ebp::context of from
 
    # restore to's registers
    movl 4(%esp), %eax          # not 8(%esp): popped return address already
                                # eax now points to to
    movl 28(%eax), %ebp         # restore ebp::context of to
    movl 24(%eax), %edi         # restore edi::context of to
    movl 20(%eax), %esi         # restore esi::context of to
    movl 16(%eax), %edx         # restore edx::context of to
    movl 12(%eax), %ecx         # restore ecx::context of to
    movl 8(%eax), %ebx          # restore ebx::context of to
    movl 4(%eax), %esp          # restore esp::context of to

    pushl 0(%eax)               # push eip

    ret

this means we save the data of from in context
and save to's data to the stack

   */