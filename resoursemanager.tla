-------------------------- MODULE resoursemanager --------------------------
(* This is a TLA specification to see if a resource manager is occupied when client request 
comes. When their is a request in queue to the resource manager, the resource manager 
allocates the resource manager to the process in the queue and sets up the request flag to 
processing. After the processing is done the flag is set to done which indicates the process is 
compelted*)

Operation == {"allocate", "release"}
(*the two possible operations on the resource manager allocate and release which means the resource
manager is either allocated or finished respectively*)

NextOperation(c) == CASE c = "allocate" -> "release"
                  [] c = "release" -> "allocate"
(*the state change from possible next operations*)
                  
VARIABLES queue, resource, pc

vars == << queue, resource, pc >>

ProcSet == {"resource"} \cup {"request"}
(*It is the tuple of possible values for resource and request at any point of time*)

Init == (* Global variables *)
        /\ queue = TRUE
        /\ resource = "allocate"
        /\ pc = [self \in ProcSet |-> CASE self = "resource" -> "Deallocate"
                                        [] self = "request" -> "Processing"]
(*Initial state of the system when their is a process in the queue and the Resource manager is empty*)

Deallocate == /\ pc["resource"] = "Deallocate"
         /\ IF queue
               THEN /\ resource' = NextOperation(resource)
                    /\ pc' = [pc EXCEPT !["resource"] = "Deallocate"]/\ UNCHANGED queue
               ELSE /\ pc' = [pc EXCEPT !["resource"] = "Done"]
                    /\ resource' = resource /\ UNCHANGED queue
(*Resource manager state after being donw with current process*)

resource_ == Deallocate

Processing == /\ pc["request"] = "Processing"
         /\ resource = "release"
         /\ queue' = FALSE
         /\ pc' = [pc EXCEPT !["request"] = "Done"]
         /\ resource' = resource
(*Resource manager state when the request gets accepted into the process manager*)

request == Processing

Next == resource_ \/ request
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)
(*Next possible states specification*)

Spec == Init /\ [][Next]_vars
(*Makes it easy to run the code without giving initial and next states while creating a model *)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
(*termination condition to end the specification*)
=============================================================================
\* Modification History
\* Last modified Tue Dec 04 19:00:56 EST 2018 by sai
\* Created Sun Dec 02 13:29:08 EST 2018 by sai
