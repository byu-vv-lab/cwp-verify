

//**********VARIABLE DECLARATION************//





int x = 0






//**********STATE VARIABLE DECLARATION************//
bit Increment_x = 0
bit End = 0


//**********EDGE DECLARATION************//
bit EdgeA = 0
bit EdgeB = 0
bit EdgeC = 0


//**********UPDATE STATE INLINE************//
inline updateState() {
    d_step {
        skip
    }
}
//**********GLOBAL PROPERTIES************//
#define inAState Increment_x \
 || End
ltl alwaysInAState {(always (inAState))}
#define fair (eventually (End_FROM_Gateway_1))
ltl fairPathExists {(always (! fair))}


// // //**********Increment_x STATE PROPERTIES************//
ltl Increment_xExists {(fair implies (always (! Increment_x)))}
ltl Increment_xMutex {
    (
        always (
            Increment_x implies (
                Increment_x
                && (! End)
            )
        )
    )
}
ltl Increment_xEdges {
    (
        fair implies (
            always (
                Increment_x implies (
                    Increment_x until (
                        End
                        || Increment_x
                    )
                )
            )
        )
    )
}


// //**********End STATE PROPERTIES************//
ltl EndExists {(fair implies (always (! End)))}
ltl EndMutex {
    (
        always (
            End implies (
                End
                && (! Increment_x)
            )
        )
    )
}
ltl EndEdges {
    (
        fair implies (
            always (
                End implies (
                    always End
                )
            )
        )
    )
}






#define Gateway_1_hasOption \
(\
    x > 5||\
    x <=5\
)


#define hasToken(place) (place != 0)

#define putToken(place) place = 1

#define consumeToken(place) place = 0



bit Start = 0
bit Increment_x_FROM_Start = 0
bit Increment_x_FROM_Gateway_1 = 0
bit Increment_x_END = 0
bit End_FROM_Gateway_1 = 0
bit Gateway_1_FROM_Increment_x = 0


inline Start_BehaviorModel() {
    skip
}

inline Increment_x_BehaviorModel() {
    x = x + 1
}

//Increment_x_END
inline Increment_x_END_BehaviorModel(){
    skip
}

//End
inline End_BehaviorModel(){
    skip
}

inline Gateway_1_BehaviorModel() {
    skip
}




init {
    atomic{
        updateState()
        run Process_1()
    }
}




proctype Process_1() {
pid me = _pid
putToken(Start)
do
:: atomic { (hasToken(Start)) ->
        Start_BehaviorModel()
        d_step {
            consumeToken(Start)
            putToken(Increment_x_FROM_Start)
        }
    }
:: atomic { (( hasToken(Increment_x_FROM_Start)||hasToken(Increment_x_FROM_Gateway_1) )
) ->
        Increment_x_BehaviorModel()
        d_step {
            consumeToken(Increment_x_FROM_Start)
            consumeToken(Increment_x_FROM_Gateway_1)
            putToken(Increment_x_END)
        }
    }
:: atomic { (hasToken(Increment_x_END)) ->
        skip
        d_step {
            consumeToken(Increment_x_END)
            putToken(Gateway_1_FROM_Increment_x)
        }
    }
:: atomic { (( hasToken(Gateway_1_FROM_Increment_x) )
) ->
        Gateway_1_BehaviorModel()
        d_step {
            consumeToken(Gateway_1_FROM_Increment_x)
            putToken(End_FROM_Gateway_1)
            putToken(Increment_x_FROM_Gateway_1)
        }
    }
:: atomic { (( hasToken(Gateway_1_FROM_Increment_x) )
    &&  (Gateway_1_hasOption)) ->
        Gateway_1_BehaviorModel()
        d_step {
            consumeToken(Gateway_1_FROM_Increment_x)
            if
                :: x > 5 -> putToken(End_FROM_Gateway_1)
                :: x <=5 -> putToken(Increment_x_FROM_Gateway_1)
            fi
        }
    }
:: atomic { (( hasToken(End_FROM_Gateway_1) )
) ->
        End_BehaviorModel()
        d_step {
            consumeToken(End_FROM_Gateway_1)
        }
    }
od
}
