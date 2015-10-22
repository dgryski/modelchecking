
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

proctype worker(byte id) {
    byte held = 0
    bool looped

    time == id;
    printf("worker %d starting\n", id);

    atomic {
        if
        :: !locks[3] -> locks[3]=id; held=3;
        :: else -> incrementTime(id); goto endExit
        fi
    }

    do
    :: held == 0 -> break
    :: else
        byte next = held - 1
        bool gotLock
        atomic {
            if
            :: !locks[next] -> locks[next]=id; gotLock=true;
            :: else
            fi
        }

        if
        :: gotLock -> locks[held] = 0; held=next;
        :: else
            if
            :: held == 1 ->
                atomic {
                    gotLock = false;
                    if
                    :: !locks[2] -> locks[2]=id; gotLock=true;
                    :: else
                    fi
                }

                if
                :: !gotLock -> atomic { assert(locks[1]==id); locks[1]=0; goto endExit; }
                :: else -> atomic { assert(locks[2] == id); locks[2]=0; }
                fi
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

    atomic {
        assert(locks[0] == id);
        locks[0] = 0;
    }

endExit:
    printf("worker %d exiting\n", id);

    assert(locks[0] != id && locks[1] != id && locks[2] != id && locks[3] != id);
}

init {
    run worker(1); run worker(2); run worker(3); run worker(4); run worker(5);
    run worker(6); run worker(7); run worker(8); run worker(9); run worker(10);
}
