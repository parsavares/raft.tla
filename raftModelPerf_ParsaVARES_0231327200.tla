--------------------------- MODULE raftModelPerf_ParsaVARES_0231327200 ---------------------------


\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further to track message counts for entry commitment.
\* Modified further to incorporate HovercRaft changes.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* A dedicated identifier for the Switch component
CONSTANTS Switch

\* The set of all nodes in the system (Raft Servers + Switch)
Node == Server \union {Switch}

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          \* --- HovercRaft Additions ---
          RecoveryRequest, RecoveryResponse
          
\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests 

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. This is a function mapping Message to Nat.
VARIABLE messages

\* Counter for how many times each server has become leader
VARIABLE leaderCount

\* maximum client requests so far
VARIABLE maxc

\* variable for tracking entry commit message counts
\* Maps <<logIndex, logTerm>> to a record tracking message counts.
\* [ sentCount |-> Nat,   \* AppendEntriesRequests sent for this entry
\*   ackCount  |-> Nat,   \* Successful AppendEntriesResponses received for this entry
\*   committed |-> Bool ] \* Flag indicating if the entry is committed
VARIABLE entryCommitStats

\* --- HovercRaft Additions ---
\* Stores payloads received but not yet ordered.
\* For Servers: payloads received from Switch.
\* For Switch: payloads received from Client.
VARIABLE pendingRequests

\* Stores payloads identified as missing by Servers for which recovery has been requested.
\* Switch does not participate in recovery this way.
VARIABLE missingRequests

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>

\* All variables; used for stuttering (asserting state hasn't changed).
\* Updated to include HovercRaft variables
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars,
          pendingRequests, missingRequests>>

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        msgs
       \* [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

min(a, b) == IF a < b THEN a ELSE b

ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }

\* The prefix of the log of server i that has been committed up to term x
CommittedTermPrefix(i, x) ==
    \* Only if log of i is non-empty, and if there exists an entry up to the term x
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
      \* then, we use the subsequence up to the maximum committed term of the leader
      LET maxTermIndex ==
          CHOOSE y \in DOMAIN log[i] :
            /\ log[i][y].term <= x
            /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    \* Otherwise the prefix is the empty tuple
    ELSE << >>

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A i \in 1..Len(seq1) : seq1[i] = seq2[i]

\* The prefix of the log of server i that has been committed
Committed(i) ==
    IF commitIndex[i] = 0
    THEN << >>
    ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Server: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests ) 
                /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Symmetry == Permutations(Server)

\* new bag of messages with one more m in it. the following from orig spec necessary for Drop
\*WithMessage(m, msgs) ==
\*    IF m \in DOMAIN msgs THEN
\*        [msgs EXCEPT ![m] = msgs[m] + 1]
\*    ELSE
\*        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\*WithoutMessage(m, msgs) ==
\*    IF m \in DOMAIN msgs THEN
\*        IF msgs[m] <= 1 THEN [i \in DOMAIN msgs \ {m} |-> msgs[i]]
\*        ELSE [msgs EXCEPT ![m] = msgs[m] - 1]
\*    ELSE
\*        msgs

InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
\* Initialize Hovercraft related variables for ALL Nodes or just Servers as appropriate
InitHovercraftVars ==
    /\ pendingRequests = [n \in Node |-> {}] \* Covers Servers and Switch
    /\ missingRequests = [i \in Server |-> {}] \* Only Servers need this    
    
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitHovercraftVars \* Add Hovercraft Vars Init
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize new variable

\* MyInit remains unchanged for the core Raft state, entryCommitStats is handled in Init.
MyInit ==
    LET ServerIds == CHOOSE ids \in [1..3 -> Server] : TRUE
        r1 == ServerIds[1]
        r2 == ServerIds[2]
        r3 == ServerIds[3]
    IN
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]  \* Start with empty messages
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |-> IF s = r2 THEN Leader ELSE Follower]
    /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
    /\ voterLog = [s \in Server |-> IF s = r2 THEN (r1 :> <<>> @@ r3 :> <<>>) ELSE <<>>]
    /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize here too
    \* Initialize Hovercraft Vars for MyInit explicitly for Nodes/Servers
    /\ pendingRequests = [n \in Node |-> {}]
    /\ missingRequests = [i \in Server |-> {}]
    
\* to be used directly in model Init the value
\*MyInit2 ==
\*    /\  commitIndex = (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  currentTerm = (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2)
\*    /\  entryCommitStats = << >>
\*    /\  leaderCount = (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  log = (r1 :> <<>> @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  matchIndex = ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) )
\*    /\  maxc = 0
\*    /\  messages = << >>
\*    /\  nextIndex = ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) )
\*    /\  state = (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower)
\*    /\  votedFor = (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1)
\*    /\  voterLog = (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  votesGranted = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
\*    /\  votesResponded = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})


----
\* Define state transitions

\* Modified to allow Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars elections, maxc, leaderCount, entryCommitStats
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars>>

\* Modified to restrict Timeout to just Followers
\* Server i times out and starts a new election. Follower -> Candidate
Timeout(i) == /\ state[i] \in {Follower} \*, Candidate
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars>>

\* Modified to restrict Leader transitions, bounded by MaxBecomeLeader
\* Candidate i transitions to leader. Candidate -> Leader
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** REQUEST VOTE **********************************************
\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** HovercRaft Additions  **********************************************
\* --- Step 1: Client sends request 'v' TO THE SWITCH ---
SwitchClientRequest(v) ==
    /\ maxc < MaxClientRequests \* Apply global request limit
    \* Update only the Switch's pending requests
    /\ pendingRequests' = [pendingRequests EXCEPT ![Switch] = @ \cup {v}]
    /\ maxc' = maxc + 1 \* Increment count when request enters the system
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   leaderCount, entryCommitStats, missingRequests>>
                   \* Note: pendingRequests for Server nodes are unchanged here.

\* --- Step 2: Switch disseminates a pending request 'v' TO ALL SERVERS ---
SwitchDisseminate(v) ==
    /\ v \in pendingRequests[Switch] \* Switch must have the request
    \* Update pendingRequests: Remove from Switch, add to all Servers
    /\ pendingRequests' = [ n \in Node |->
                              IF n = Switch THEN pendingRequests[n] \ {v}
                              ELSE IF n \in Server THEN pendingRequests[n] \cup {v}
                                   ELSE pendingRequests[n] \* Should not happen, but defensive
                          ]
    \* Note: maxc was already incremented by SwitchClientRequest
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   maxc, leaderCount, entryCommitStats, missingRequests>>

\* remove ClientMulticast(v) == ... (This action is now replaced by the two above)

\*\* --- HovercRaft Change: Client Interaction ---
\*\* Simulate the Switch multicasting a client request payload 'v' to all servers.
\*ClientMulticast(v) ==
\*    /\ maxc < MaxClientRequests \* Still apply global request limit
\*    /\ pendingRequests' = [i \in Server |-> pendingRequests[i] \cup {v}]
\*    /\ maxc' = maxc + 1 \* Increment count when request enters the system
\*    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
\*                   leaderCount, entryCommitStats, missingRequests>>


\* --- HovercRaft Change: Leader orders a request ---
\* Leader 'i' chooses a pending request 'v' to include in its log.
\* This replaces the original ClientRequest logic.
LeaderOrderRequest(i, v) ==
    /\ state[i] = Leader
    /\ v \in pendingRequests[i] \* Leader must have received the multicast
    /\ LET entryTerm == currentTerm[i]
           \* New entry structure: term, value (as ID), payload (actual data)
           \* Here, 'v' (from Value set) serves as both the ID for 'value' field
           \* and the content for 'payload' field.
           entry == [term |-> entryTerm, value |-> v, payload |-> v] 
           \* Check if this exact value (request ID, which is 'v') is already *ordered* in the log
           \* by looking at the '.value' field of existing log entries.
           alreadyOrdered == \E idx \in DOMAIN log[i] : log[i][idx].value = v
           newLog == IF alreadyOrdered THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == IF alreadyOrdered THEN 0 ELSE Len(log[i]) + 1 \* 0 if not new
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \ {v}] \* Remove from leader's pending
        /\ entryCommitStats' =
              IF /\ newEntryIndex > 0 \* Only add stats for newly ordered entries
                 /\ newEntryKey \notin DOMAIN entryCommitStats \* Avoid overwriting if somehow re-ordered
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
        /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex,
                       maxc, leaderCount, missingRequests>> \* maxc already incremented previously



\***************************** AppendEntries **********************************************

\* Original ClientRequest - Keep definition but EXCLUDE from Next state for HovercRaft run
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>

\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry. It was up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\* --- HovercRaft Change: AppendEntries sends metadata only ---
\* Leader i sends j an AppendEntries request containing exactly 1 *metadata* entry.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0
    /\ nextIndex[i][j] <= Len(log[i])
    \* /\ matchIndex[i][j] < nextIndex[i][j] \* Original condition - can remove or keep, depends on retry logic desired. Let's keep it simple for now.
    /\ LET entryIndex == nextIndex[i][j]
           entryMetadata == log[i][entryIndex] \* This is [term |-> t, value |-> v]
           entries == << entryMetadata >> \* Send only the metadata entry
           entryKey == <<entryIndex, entryMetadata.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,       \* Metadata only
                mlog           |-> log[i],        \* Keep for history variable/proofs if needed
                mcommitIndex   |-> Min({commitIndex[i], entryIndex -1 }), \* Commit up to previous entry
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount,
                   pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here


\* --- HovercRaft Actions: Recovery Mechanism (Helper Action) ---
\* Note: This is defined separately for clarity but used within HandleAppendEntriesRequest
\* Follower i sends a RecoveryRequest for payload v to leader j
SendRecoveryRequest(i, j, v) ==
    /\ Send([mtype         |-> RecoveryRequest,
             mterm         |-> currentTerm[i],
             mRequestValue |-> v,
             msource       |-> i,
             mdest         |-> j])
    \* This action only modifies 'messages'. Other UNCHANGED are handled by the caller.


\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* --- HovercRaft Change: HandleAppendEntriesRequest checks pendingRequests ---
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        acceptRequestLogic(newState) ==
            /\ m.mterm = currentTerm[i]
            /\ newState = Follower \* Must be follower to accept
            /\ logOk
            /\ LET index == m.mprevLogIndex + 1
               IN \/ \* Heartbeat or already have this exact entry (now [term, value, payload])
                     /\ \/ m.mentries = << >> \* Heartbeat
                        \/ /\ Len(log[i]) >= index
                           /\ log[i][index].term = m.mentries[1].term   \* Compare term
                           /\ log[i][index].value = m.mentries[1].value \* Compare value (ID)
                           \* Assuming if term and value (ID) match, the payload also matches.
                           \* If payload could differ for same term/ID, add: /\ log[i][index].payload = m.mentries[1].payload
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                     /\ Reply([mtype           |-> AppendEntriesResponse,
                               mterm           |-> currentTerm[i],
                               msuccess        |-> TRUE,
                               mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                               msource         |-> i,
                               mdest           |-> j], m)
                     /\ UNCHANGED <<serverVars, log, pendingRequests, missingRequests>>
                  \/ \* Conflict: remove entries (term mismatch for the same index)
                     /\ m.mentries /= << >>
                     /\ Len(log[i]) >= index
                     /\ log[i][index].term /= m.mentries[1].term
                     /\ LET newLog == SubSeq(log[i], 1, index - 1)
                        IN log' = [log EXCEPT ![i] = newLog]
                     /\ UNCHANGED <<serverVars, commitIndex, messages, pendingRequests, missingRequests>>
                  \/ \* Append new entry: Check for payload (identified by 'value' field) before appending
                     /\ m.mentries /= << >>
                     /\ Len(log[i]) = m.mprevLogIndex \* This is the point to append a new entry
                     /\ LET receivedEntry == m.mentries[1]      \* This is [term, value, payload]
                           requestId == receivedEntry.value     \* This is the ID used for matching pendingRequests
                        IN \/ \* Payload IS available (identified by requestId in pendingRequests)
                              /\ requestId \in pendingRequests[i] \* Condition
                              /\ log' = [log EXCEPT ![i] = Append(log[i], receivedEntry)] \* Append the full [term,value,payload] record
                              /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \ {requestId}] \* Remove raw payload from buffer by ID
                              /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                              /\ Reply([mtype           |-> AppendEntriesResponse,
                                        mterm           |-> currentTerm[i],
                                        msuccess        |-> TRUE,
                                        mmatchIndex     |-> index,
                                        msource         |-> i,
                                        mdest           |-> j], m)
                              /\ UNCHANGED <<serverVars, missingRequests>>

                           \/ \* Payload is MISSING
                              /\ requestId \notin pendingRequests[i] \* Condition
                              /\ Reply([mtype           |-> AppendEntriesResponse,
                                        mterm           |-> currentTerm[i],
                                        msuccess        |-> FALSE,
                                        mmatchIndex     |-> m.mprevLogIndex,
                                        msource         |-> i,
                                        mdest           |-> j], m)
                              /\ IF requestId \notin missingRequests[i]
                                 THEN /\ SendRecoveryRequest(i, j, requestId) \* Request recovery using the ID
                                      /\ missingRequests' = [missingRequests EXCEPT ![i] = missingRequests[i] \cup {requestId}]
                                 ELSE /\ UNCHANGED <<messages, missingRequests>>
                              /\ UNCHANGED <<serverVars, log, commitIndex, pendingRequests>>

    IN /\ m.mterm <= currentTerm[i]  \* Overall precondition
       /\ ( \* Start of main disjunction for handling paths
             \/ /\ \* Path 1: Reject request
                   ( \/ m.mterm < currentTerm[i]
                     \/ /\ m.mterm = currentTerm[i]
                        /\ state[i] = Follower
                        /\ \lnot logOk
                   )
                   /\ Reply([mtype           |-> AppendEntriesResponse,
                             mterm           |-> currentTerm[i],
                             msuccess        |-> FALSE,
                             mmatchIndex     |-> 0,
                             msource         |-> i,
                             mdest           |-> j], m)
                   /\ UNCHANGED <<serverVars, logVars, pendingRequests, missingRequests>>

             \/ /\ \* Path 2: Step down if candidate
                   m.mterm = currentTerm[i]
                   /\ state[i] = Candidate
                   /\ state' = [state EXCEPT ![i] = Follower]
                   /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, pendingRequests, missingRequests>>

             \/ /\ \* Path 3: Accept request (or trigger recovery)
                   acceptRequestLogic(state[i])
                   /\ UNCHANGED <<candidateVars, leaderVars>>

          )
       /\ UNCHANGED <<instrumentationVars>>

\* Leader i handles RecoveryRequest for value v from follower j
\* Leader checks its *log* to see if it has ordered this value.
\* Simplification: Assume leader has the payload if it's in its log.
HandleRecoveryRequest(i, j, m) ==
    LET requestedValue == m.mRequestValue
        \* Check if the leader has ordered this value (i.e., it's in the log)
        hasValue == \E idx \in DOMAIN log[i] : log[i][idx].value = requestedValue
    IN /\ m.mterm <= currentTerm[i] \* Ignore stale requests, respond with current term if lower
       /\ IF hasValue
          THEN Reply([mtype         |-> RecoveryResponse,
                      mterm         |-> currentTerm[i],
                      mRequestValue |-> requestedValue,
                      \* No separate payload field needed if Value is the payload
                      msource       |-> i,
                      mdest         |-> j], m)
          ELSE Discard(m) \* Leader doesn't have it (maybe lost leadership?), ignore.
       /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars,
                      pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here

\* Follower i handles RecoveryResponse for value v from leader j
HandleRecoveryResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i] \* Precondition
    /\ ( LET recoveredValue == m.mRequestValue \* Group the LET...IN block
         IN /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \cup {recoveredValue}]
            /\ missingRequests' = [missingRequests EXCEPT ![i] = missingRequests[i] \ {recoveredValue}]
            /\ Discard(m)
       ) \* End group
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>> \* pendingRequests is UNCHANGED here


\* HandleAppendEntriesResponse: No changes needed for HovercRaft core logic.
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Leader \* Only leaders process these responses
    /\ \/ /\ m.msuccess \* successful
          /\ LET newMatchIndex == m.mmatchIndex
                 \* Find the corresponding entry key using the acknowledged index
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats
       \/ /\ \lnot m.msuccess \* not successful
          \* If follower rejected due to missing payload, leader will eventually retry AppendEntries
          \* for that index after nextIndex[i][j] is potentially decremented here.
          \* If follower rejected due to log mismatch (m.mterm > currentTerm[j] response implicit),
          \* leader might decrement nextIndex based on that future response or current logic.
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount,
                   pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           \* Identify the keys in entryCommitStats corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          \* Update the 'committed' flag for the relevant entries in entryCommitStats
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, pendingRequests, missingRequests>>
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, pendingRequests, missingRequests>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, pendingRequests, missingRequests>>


\* Receive a message. Handles messages between Servers. Switch doesn't receive Raft messages.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN /\ i \in Server /\ j \in Server \* Explicitly state receiver/sender are servers
       /\ ( \* Check for term update first
             \/ UpdateTerm(i, j, m)
             \* Handle existing Raft message types
             \/ /\ m.mtype = RequestVoteRequest
                /\ HandleRequestVoteRequest(i, j, m)
             \/ /\ m.mtype = RequestVoteResponse
                /\ \/ DropStaleResponse(i, j, m)
                   \/ HandleRequestVoteResponse(i, j, m)
             \/ /\ m.mtype = AppendEntriesRequest
                /\ HandleAppendEntriesRequest(i, j, m) \* HovercRaft updated logic
             \/ /\ m.mtype = AppendEntriesResponse
                /\ \/ DropStaleResponse(i, j, m)
                   \/ HandleAppendEntriesResponse(i, j, m)
             \* --- HovercRaft Additions: Handle Recovery Messages ---
             \/ /\ m.mtype = RecoveryRequest
                /\ HandleRecoveryRequest(i, j, m)
             \/ /\ m.mtype = RecoveryResponse
                /\ HandleRecoveryResponse(i, j, m)
          )


\* Defines how the variables may transition.
Next ==
           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \* --- HovercRaft Changes: Switch Interaction ---
           \/ \E v \in Value : SwitchClientRequest(v)   \* Client sends to Switch
           \/ \E v \in Value : SwitchDisseminate(v)     \* Switch sends to Servers
           \* --- Leader orders request received from Switch ---
           \/ \E i \in Server, v \in Value : LeaderOrderRequest(i, v)
           \* --- End HovercRaft Changes ---
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
           \/ \E m \in ValidMessage(messages) : Receive(m) \* Server-to-Server messages
\*           \/ \E m \in ValidMessage(messages) : DuplicateMessage(m)
\*           \/ \E m \in ValidMessage(messages) : DropMessage(m)

\* A restricted Next for targeted testing of core HovercRaft flow
MyNext ==
\*           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
\*           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
\*           \/ \E i \in Server : BecomeLeader(i)
           \* --- HovercRaft Changes: Switch Interaction ---
           \/ \E v \in Value : SwitchClientRequest(v)   \* Client sends to Switch
           \/ \E v \in Value : SwitchDisseminate(v)     \* Switch sends to Servers
           \* --- Leader orders request received from Switch ---
           \/ \E i \in Server, v \in Value : LeaderOrderRequest(i, v)
           \* --- End HovercRaft Changes ---
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j) \* Sends metadata
           \/ \E m \in {msg \in ValidMessage(messages) : \* Focus on HovercRaft message processing
                       msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse,
                                      RecoveryRequest, RecoveryResponse}} : Receive(m)
\*           \/ \E m \in ValidMessage(messages) : DuplicateMessage(m)
\*           \/ \E m \in ValidMessage(messages) : DropMessage(m)



\* A specific Next state for testing only the SwitchClientRequest action
MyNextAddSwitch ==
    \/ \E v \in Value : SwitchClientRequest(v)
    \* Stuttering step for all variables if the action isn't enabled
    \/ UNCHANGED vars

\* New Spec for testing just the SwitchClientRequest action
SpecAddSwitch == Init /\ [][MyNextAddSwitch]_vars

\* Example of a fake invariant for testing SpecAddSwitch
\* Verify maxc increases when SwitchClientRequest runs.
\* This invariant should eventually be violated.
MaxCInvariantForSwitchTest == maxc = 0

\* Add this theorem for the new test spec
THEOREM SpecAddSwitch => []MaxCInvariantForSwitchTest



\* The specification must start with the initial state and transition according
\* to Next. Implicitly uses 'vars' defined in raftVariables.
Spec == Init /\ [][Next]_vars

MySpec == MyInit /\ [][MyNext]_vars

\* -------------------- Invariants --------------------
\* These standard Raft invariants should still hold for HovercRaft,
\* as it aims to maintain the core safety properties.

\* At most one leader per term. (Only applies to Servers)
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* If two logs contain an entry with the same index and term,
\* then the logs are identical in all preceding entries. (Only applies to Servers)
LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* If an entry is committed, it must be present in the logs of future leaders. (Only applies to Servers)
\* (Slightly adapted wording for checking prefixes against leader's log in its term)
LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])


\* Committed logs must be prefixes of one another. (Only applies to Servers)
LogInv ==
    \A i, j \in Server :
        \/ CheckIsPrefix(Committed(i),Committed(j))
        \/ CheckIsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
\* Theorem for the main specification
THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv)


\*instrumentation and performance invariants

\* A leader's maxc should remain under MaxClientRequests
MaxCInv == (\E i \in Server : state[i] = Leader) => maxc <= MaxClientRequests

\* No server can become leader more than MaxBecomeLeader times
LeaderCountInv == \E i \in Server : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

\* No server can have a term exceeding MaxTerm
MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

\* Check lower bound for message counts on committed entries ----
\* For any entry that has been marked as committed, verify that either the number
\* of AppendEntries requests sent OR the number of successful acknowledgments received
\* is at least the minimum number of followers required to form a majority.
\* will fail when an entry was sent twice to a follower and no response was acked yet, which is normal
EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Server) - 1
        MinFollowersForMajority == Cardinality(Server) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

\* Check that committed entries received acknowledgments from a majority of followers.
EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Server)
        \* Minimum number of *followers* needed (in addition to the leader)
        \* to reach a majority for committing an entry.
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in Server : commitIndex[i] /= 1 \*

\*Modify LeaderCommited == \E i \in Server : commitIndex[i] /= 1
\*and run with MySpec OR

\*Use the following modified Init with MyNext for finding an error trace with LeaderCommited == \E i \in Server : commitIndex[i] /= 2 violated
(*

/\  commitIndex = [r1 |-> 1, r2 |-> 1, r3 |-> 1]
/\  currentTerm = [r1 |-> 2, r2 |-> 2, r3 |-> 2]
/\  entryCommitStats = ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] )
/\  leaderCount = [r1 |-> 1, r2 |-> 0, r3 |-> 0]
/\  log = [ r1 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ]
/\  matchIndex = [ r1 |-> [r1 |-> 0, r2 |-> 1, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ]
/\  maxc = 2
/\  messages = ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 )
/\  nextIndex = [ r1 |-> [r1 |-> 1, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ]
/\  state = [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower]
/\  votedFor = [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"]
/\  voterLog = [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>]
/\  votesGranted = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
/\  votesResponded = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]

*)
=============================================================================
\* Created by Ovidiu-Cristian Marcu