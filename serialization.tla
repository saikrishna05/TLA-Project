-------------------------------- MODULE serialization --------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLES 
    location,    \* the items in the left and right location
    carrier,  \* the item to carry in the boat 
    currentLocation,  \* the location where the currentLocation currently is
    PreviousPacket,     \* the PreviousPacket item carried 
    log       \* the shippments log trace
  
Allowed(S) == \* Check if the items in set S are allowed to be alone
    ~({"Packet1", "Packet3"} \subseteq S \/ {"Packet3", "Packet2"} \subseteq S)

OtherLocation(M) == \* location toggle
    IF M = "Left" THEN "Right" ELSE "Left"
        
ConsistencyOK == \* Invariant to check the model consistency
    /\ currentLocation \in {"Left", "Right"}
    /\ Cardinality(location.Left) + Cardinality(location.Right) = 3
    /\ Allowed(location[OtherLocation(currentLocation)]) \* are the items in the other location allowed to be alone?
          
SolutionNotFound == \* The goal is to move the items from the left location to the right, leaving left empty
    Cardinality(location.Left) > 0
                    
Init == \* The initial state
    /\ location = [Left |-> {"Packet1","Packet3","Packet2"}, Right |-> {}]   
    /\ currentLocation = "Left"
    /\ carrier = ""
    /\ PreviousPacket = ""
    /\ log = << >>
       
Selectcarrier == \* Select a viable item to carry if none was selected yet (excluding the PreviousPacket one carried)
    /\ carrier = ""
    /\ \E p \in location[currentLocation] : Allowed(location[currentLocation] \ {p}) /\ (p # PreviousPacket) /\ carrier' = p
    /\ UNCHANGED <<location, currentLocation, log, PreviousPacket>>

Transfer1 == \* Sending the first available packet
    /\ carrier = ""
    /\ PreviousPacket # ""
    /\ Allowed(location[currentLocation])
    /\ currentLocation' = OtherLocation(currentLocation)
    /\ PreviousPacket' = ""
    /\ log' = Append(log, "")
    /\ PrintT(log')
    /\ UNCHANGED <<location, carrier>>
                                           
Transfer2 == \*sending the packet back since it is not in order
    /\ carrier # ""
    /\ location' = [location EXCEPT 
                     ![currentLocation] = @ \ { carrier }, 
                     ![OtherLocation(currentLocation)] = @ \union { carrier }] 
    /\ currentLocation' = OtherLocation(currentLocation)
    /\ log' = Append(log, carrier)
    /\ PreviousPacket' = carrier
    /\ carrier' = ""
    /\ PrintT(log')
                              
Next == \* Get to work! 
    Selectcarrier \/ Transfer2 \/ Transfer1

=============================================================================
\* Modification History
\* Last modified Wed Dec 05 16:57:56 EST 2018 by sai

