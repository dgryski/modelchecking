

/* true if crossed */
bool flashlight;
bool person1;
bool person2;
bool person5;
bool person10;

byte time;

inline cross(a, b, t) {
    atomic {
        time = time + t
        flashlight = !flashlight
        a = !a
        b = !b
    }
}

inline crossAlone(a,t) {
    atomic {
        time = time + t
        flashlight =!flashlight
        a = !a
    }
}

inline log() {
    printf("1:%d 2:%d 5:%d 10:%d t:%d\n", person1, person2, person5, person10, time);
}

active proctype bridge() {
    do
    :: time < 32 -> if
            :: person1 == flashlight -> log(); printf("1\n");  crossAlone(person1, 1)
            :: person1 == flashlight && person1 == person2 -> log(); printf("1+2\n"); cross(person1, person2,  2)
            :: person1 == flashlight && person1 == person5 -> log();  printf("1+5\n"); cross(person1, person5,  5)
            :: person1 == flashlight && person1 == person10 -> log();  printf("1+10\n"); cross(person1, person10,  10)

            :: person2 == flashlight -> log();  printf("2\n"); crossAlone(person2, 2)
            :: person2 == flashlight && person2 == person5 -> log();  printf("2+5\n"); cross(person2, person5,  5)
            :: person2 == flashlight && person2 == person10 -> log();  printf("2+10\n"); cross(person2, person10,  10)

            :: person5 == flashlight -> log(); printf("5\n"); crossAlone(person5, 5)
            :: person5 == flashlight && person5 == person10 -> log();  printf("5+10\n"); cross(person5, person10,  10)

            :: person10 == flashlight -> log(); printf("10\n"); crossAlone(person10, 10)
         fi
    :: else -> atomic { person1=0;person2=0;person5=0;person10=0;flashlight=0;time=0; }
    od
}

never {
    do
    :: assert(!(person1 && person2 && person5 && person10 && (time == 17)))
    od
}
