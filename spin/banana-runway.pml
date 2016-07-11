/* too many bananas */
/* model more closely matching https://github.com/salesforce/runway-model-toomanybananas/blob/master/toomanybananas.model */

/* count of bananas in the house */
byte bananas = 2;

/* is there a note? */
bool note;

mtype = { hungry, happy, goingToStore, returningFromStore }

inline buyBananas(p) {
    if
    :: p.carrying = 0
    :: p.carrying = 1
    :: p.carrying = 2
    :: p.carrying = 3
    :: p.carrying = 4
    :: p.carrying = 5
    :: p.carrying = 6
    :: p.carrying = 7
    :: p.carrying = 8
    fi
}

typedef person {
    mtype state = happy
    byte carrying
}

active [4] proctype worker() {

    person p;

    bool ate;

    do
    :: if
        :: p.state == happy -> atomic {
                p.state = hungry;
            }
        :: p.state == hungry -> atomic {
                ate=false;
                if
                :: bananas == 0 ->
                    if
                    :: note -> /* roommate at store, try again later */
                    :: else ->
                        note = true
                        p.state = goingToStore
                    fi
                :: else ->
                    bananas = bananas - 1;
                    ate = true;
                fi
            }
            if
            :: ate == true ->
progress:      p.state = happy;
            :: else ->
            fi
        :: p.state == goingToStore -> atomic {
                buyBananas(p);
                p.state = returningFromStore;
            }
        :: p.state == returningFromStore -> atomic {
            bananas = bananas + p.carrying;
            note = false;
            p.state = hungry;
            }
        fi
    od
}

never {
    do
    :: assert(bananas <= 8);
    od
}
