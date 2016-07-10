
#define PHILOSOPHERS 5

bool forks[PHILOSOPHERS];

active [PHILOSOPHERS] proctype phil() {

    byte fork1, fork2;

    fork1 = _pid;
    fork2 = (_pid + 1) % PHILOSOPHERS;

    /* without resource ordering the process can deadlock */
    if
    :: fork2 < fork1 -> d_step {
        byte swap;
        swap = fork1;
        fork1 = fork2;
        fork2 = swap;
        }
    :: else  ->
    fi

    do
    :: true ->
       atomic { forks[fork1]==false -> forks[fork1]=true; }
       atomic { forks[fork2]==false -> forks[fork2]=true; }
progressEat: printf("phil %d eating\n", _pid);
       d_step {
            forks[fork1]=false;
            forks[fork2]=false;
        }
    od
}
