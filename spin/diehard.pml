
int three;
int five;

inline threeToFive() {
    int space = 5 - five;
    if
    :: three > 0 && space > 0 && space > three -> printf("5:%d 3:%d three -> five %d\n", five, three, three); five = five + three; three = 0;
    :: three > 0 && space > 0 && space <= three -> printf("5:%d 3:%d three -> five %d\n", five, three, space); five = five + space; three = three - space;
    fi
}

inline fiveToThree() {
    int space = 3 - three;
    if
    :: five > 0 && space > 0 && space > five -> printf("5:%d 3:%d five -> three %d\n", five, three, five); five = 0; three = three + five;
    :: five > 0 && space > 0 && space <= five -> printf("5:%d 3:%d five -> three %d\n", five, three, space); five = five - space; three = three + space;
    fi
}

active proctype jugs() {
    do
    :: if
            :: three == 0 -> printf("5:%d 3:%d fill three\n", five, three); three = 3;
            :: three > 0 -> printf("5:%d 3:%d empty three\n", five, three); three = 0;
            :: three > 0 -> threeToFive();
            :: five == 0 -> printf("5:%d 3:%d fill five\n", five, three); five = 5;
            :: five > 0 -> printf("5:%d 3:%d empty five\n", five, three); five = 0;
            :: five > 0 -> fiveToThree();
        fi
    od
}

never {
    do
    :: assert(five != 4); assert(five <= 5); assert(three <= 3);
    od
}
