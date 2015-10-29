
/* 0 if not held, otherwise id of worker */
byte locks[4];

byte lastrun
byte time = 1

// worker id has just finished a bit of work, increment time
inline incrementTime(id) {
    atomic {
        if
        :: time == id -> printf("worker %d incrementing time to %d\n", id, time+1); time = time + 1;
        :: else
        fi
    }
}

inline trylock(lock,id) {
        atomic {
            gotLock = false
            if
            :: !locks[lock] -> locks[lock]=id; gotLock=true;
            :: else
            fi
        }
}

inline release(lock, id) {
    atomic {
       assert(locks[lock] == id)
       locks[lock]=0;
    }
}

proctype worker(byte id) {
    byte held = 0
    bool looped
    bool gotLock

    time == id;
    printf("worker %d starting\n", id);

    trylock(3,id)

    if
    :: !gotLock -> incrementTime(id); goto endExit
    :: else
    fi
    held=3

    do
    :: held == 0 -> break
    :: else
        byte next = held - 1
        trylock(next,id)

        if
        :: gotLock -> release(held,id); held=next;
        :: else
            if
            :: held == 1 ->
                atomic {
                    trylock(2, id)

                    if
                    :: !gotLock -> assert(locks[2] > id)
                    :: else
                    fi
                }

                if
                :: !gotLock -> release(1, id); goto endExit
                :: else
                fi
                release(2, id)
            :: else
            fi
        fi

        // allow the next worker to start
        if
        :: !looped -> looped=true; incrementTime(id);
        :: else
        fi
    od

    assert(locks[0] == id && locks[1] != id && locks[2] != id && locks[3] != id);

    atomic {
        assert(id > lastrun)
        lastrun = id
    }

    printf("worker %d working\n", id);

    release(0, id)

endExit:
    printf("worker %d exiting\n", id);

    assert(locks[0] != id && locks[1] != id && locks[2] != id && locks[3] != id);
}

init {
    run worker(1); run worker(2); run worker(3); run worker(4); run worker(5);
    run worker(6); run worker(7); run worker(8); run worker(9); run worker(10);
}
