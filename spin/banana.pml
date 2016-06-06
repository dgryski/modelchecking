/* too many bananas */

/* count of bananas in the house */
byte bananas;

/* who wrote the note */
#define NOBODY 255
byte note = NOBODY;

mtype = { hungry, happy, writingNote, goingToStore, returningFromStore }

inline emptyBananaBag() {

    int b;

    atomic {

    if
    :: true -> b = 0
    :: true -> b = 1
    :: true -> b = 2
    :: true -> b = 3
    :: true -> b = 4
    :: true -> b = 5
    :: true -> b = 6
    :: true -> b = 7
    :: true -> b = 8
    fi

    bananas = bananas + b

    printf("emptying banana bag with %d bananas (total=%d)\n", b, bananas);

    }
}

active [4] proctype roommate() {

    mtype state = happy

    do
    :: if
        :: state == happy ->
                printf("worker %d happy -> hungry\n", _pid);
                state = hungry;
        :: state == hungry ->
                printf("worker %d hungry\n", _pid);
                if
                :: atomic { bananas > 0 -> bananas = bananas - 1; };
                    printf("worker %d ate a banana\n", _pid);
progress:           state = happy;
                :: else ->
                    state = writingNote;
                    printf("worker %d thinking of going to the store\n", _pid);
                fi
        :: state == writingNote ->
            if
            :: atomic { note==NOBODY -> note = _pid; }
                state=goingToStore;
                printf("worker %d writing note and heading to store\n", _pid);
            :: else ->
                state = hungry;
                printf("worker %d sees %d is already at the store\n", _pid, note);
                bananas > 0;
            fi
        :: state == goingToStore ->
            if
            :: bananas > 0 ->
                printf("worker %d found bananas after writing note\n", _pid);
                assert(note==_pid); note=NOBODY;
                state=hungry;
            :: else ->
                printf("worker %d buying bananas\n", _pid);
                state=returningFromStore;
            fi
        :: state == returningFromStore ->
            printf("worker %d emptying banana bag\n", _pid);
            emptyBananaBag();
            assert(note==_pid); note=NOBODY;
            state = hungry;
        fi
    od
}

never {
    do
    :: assert(bananas <= 8);
    od
}
