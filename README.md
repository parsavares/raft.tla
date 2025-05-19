# HovercRaft TLA+ Specification

## Overview

This project implements the HovercRaft consensus algorithm using TLA+. The main goal of HovercRaft is to improve the scalability of Raft, particularly the leader's bandwidth bottleneck, by separating the dissemination of large client request payloads from the ordering metadata. This implementation specifically models the "Switch" component as a distinct entity, following specific design requirements.

## HovercRaft vs. Standard Raft: The Core Idea

*   **Standard Raft:** The client sends its request (including the full data payload) to the leader. The leader includes this payload in its log and replicates the log entry (including the payload) to followers. The leader is responsible for both ordering *and* data dissemination.
*   **HovercRaft (as implemented):**
    1.  The client sends its request payload *only* to a distinct **Switch** entity.
    2.  The Switch entity buffers this request.
    3.  The Switch then disseminates the payload to *all Raft Servers* (leader and followers) simultaneously.
    4.  Servers temporarily store these received payloads in their `pendingRequests` buffer.
    5.  The leader is then only responsible for ordering; it selects payloads *it has received from the Switch* and sends small *metadata* messages (referencing the client request payload, e.g., using the payload value itself as an ID) to followers via standard Raft `AppendEntries`.
    6.  Followers match the incoming metadata with the payloads stored in their `pendingRequests` buffer to reconstruct the ordered log.

## Key Changes Implemented

*   **Distinct Switch Entity:** Modeled the "Switch" as a specific constant value (`Switch`) distinct from the Raft `Server` set. Introduced a `Node` set (`Server \union {Switch}`).
*   **Two-Step Payload Dissemination:**
    *   `SwitchClientRequest`: Action for client sending payload *only* to the Switch.
    *   `SwitchDisseminate`: Action for the Switch forwarding a buffered payload to *all* Raft Servers.
*   **Payload/Metadata Separation:** Modified log entries (`LeaderOrderRequest`) and `AppendEntries` messages to handle only metadata (references to payloads) instead of full payloads.
*   **Server Buffering:** Introduced a `pendingRequests` state variable (a function mapping `Node` to a set of payloads) to buffer payloads: on the Switch (from clients) and on Servers (from the Switch).
*   **Matching Logic:** Implemented logic within `HandleAppendEntriesRequest` for followers to match incoming ordering metadata from the leader with their buffered payloads (`pendingRequests[follower_id]`).
*   **Recovery Mechanism:** Added messages (`RecoveryRequest`, `RecoveryResponse`) and logic (`Handle*`) for followers to request missing payloads from the leader if they didn't receive them via the Switch dissemination.

## Detailed Changes by Module

Here's a breakdown of the significant changes made to the original Raft TLA+ files:

### `raftConstants.tla`

*   **Added Constants:** `Switch`, `RecoveryRequest`, `RecoveryResponse`.
*   **Added Definition:** `Node == Server \union {Switch}`.
*   **Why:** Introduced a distinct identifier for the Switch, defined the set of all entities, and added message types for payload recovery.

### `raftVariables.tla`

*   **Added/Modified Variables:**
    *   `pendingRequests`: Declared. Intended structure is `[Node -> SUBSET Value]`. Stores client requests on the Switch, and disseminated requests on Servers.
    *   `missingRequests`: Declared. Intended structure is `[Server -> SUBSET Value]`. Used by followers to track payloads for recovery.
*   **Updated `vars`:** Includes these new variables.

### `raftInit.tla`

*   **Initialization:** Added initialization in `Init` and `MyInit`:
    *   `pendingRequests = [n \in Node |-> {}]`
    *   `missingRequests = [i \in Server |-> {}]`
*   **Why:** Ensures variables start in a known, empty state.

### `raftActionsSolution.tla`

*   **`SwitchClientRequest(v)` (New):** Client sends `v` only to `pendingRequests[Switch]`. Increments `maxc`.
*   **`SwitchDisseminate(v)` (New):** Switch moves `v` from `pendingRequests[Switch]` to `pendingRequests[i]` for all `i \in Server`.
*   **`ClientMulticast(v)` (Replaced):** Replaced by the two actions above.
*   **`LeaderOrderRequest(i, v)` (Modified):** Leader `i` orders `v` from its `pendingRequests[i]`, adds *metadata* to `log[i]`, removes `v` from `pendingRequests[i]`.
*   **`AppendEntries(i, j)` (Modified):** Leader `i` sends *only metadata* from `log[i]` to server `j`.
*   **`HandleAppendEntriesRequest(i, j, m)` (Modified):** Follower `i` checks `pendingRequests[i]` for payload referenced in metadata `m`. If present, appends metadata to log and removes from pending. If missing, replies `FALSE` and triggers recovery (`SendRecoveryRequest`).
*   **`SendRecoveryRequest(i, j, v)` (New):** Creates and sends `RecoveryRequest`.
*   **`HandleRecoveryRequest(i, j, m)` (New):** Leader `i` handles request from `j`, checks log, sends `RecoveryResponse` if found.
*   **`HandleRecoveryResponse(i, j, m)` (New):** Follower `i` handles response from `j`, adds payload to `pendingRequests[i]`, removes from `missingRequests[i]`.
*   **`ClientRequest(i, v)` (Inactive):** Definition kept but excluded from `Next`/`MyNext`.

### `raftSpec.tla`

*   **`Receive(m)` (Modified):** Added routing for `RecoveryRequest`/`Response`. Added `i \in Server`, `j \in Server` checks.
*   **`Next` / `MyNext` (Modified):** Use `SwitchClientRequest`, `SwitchDisseminate`, `LeaderOrderRequest`.
*   **`SpecAddSwitch` / `MyNextAddSwitch` (Added):** Minimal spec for testing `SwitchClientRequest`.

### Configuration (`.cfg` File / Model Overview)

*   **Constants:** Requires defining model values for `Server`, `Switch`, `Value`, message types, bounds (`MaxClientRequests`, etc.).
*   **Specification:** Target `MySpec` (full check) or `SpecAddSwitch` (test).
*   **Invariants:** Select safety invariants (`LogInv`, etc.) for `MySpec` or test invariant for `SpecAddSwitch`.

## How to Run the Model

1.  **Open TLA+ Toolbox.**
2.  **Open Spec:** Open `raftSpec.tla`.
3.  **Create/Open Model.**
4.  **Configure Model:**
    *   **Behavior Spec:** `MySpec` or `SpecAddSwitch`.
    *   **Constants:** Define `Server`, `Switch`, `Value`, bounds, etc. (e.g., `Server <- {"r1", "r2", "r3"}`, `Switch <- "sw"`, `Value <- {"v1", "v2"}`, `MaxClientRequests <- 2`).
    *   **View:** `vars`.
    *   **Constraints:** Add `MyConstraint`.
    *   **Invariants:** Select appropriately (Safety invariants for `MySpec`, `MaxCInvariantForSwitchTest` for `SpecAddSwitch`).
5.  **Run TLC.**
6.  **Analyze:** Check results. No errors on `MySpec` (with safety invariants) indicates success. Violation of `MaxCInvariantForSwitchTest` on `SpecAddSwitch` is expected.
![image](https://github.com/user-attachments/assets/e98ac05e-f675-4ecf-9e12-72a617450fb1)
![image](https://github.com/user-attachments/assets/b2a5b0ad-f105-442a-ac1b-ecbbb4e08e3c)

## Project Update: HovercRaft TLA+ Model - [19/05/2025]

This commit finalizes the implementation of the HovercRaft protocol extensions to the base Raft TLA+ model, focusing on the introduction of an explicit Switch component and a specific log entry structure as discussed.

### Core HovercRaft Implementation:

The model implements the following key aspects of HovercRaft:

1.  **Switch Component (`Switch` constant):**
    *   Clients send requests (`Value` `v`) to the Switch component (`SwitchClientRequest` action).
    *   The Switch buffers these raw requests in `pendingRequests[Switch]`.
    *   The Switch disseminates these raw request payloads (`v`) to all Raft servers (Leader and Followers), populating their `pendingRequests` buffers (`SwitchDisseminate` action).

2.  **Leader-Driven Ordering with Metadata:**
    *   The Leader selects a raw request `v` from its own `pendingRequests` buffer.
    *   It then creates a structured log entry.

3.  **Follower Payload Matching:**
    *   Followers maintain their `pendingRequests` buffer with raw payloads received from the Switch.
    *   When a Follower receives an `AppendEntriesRequest` from the Leader containing an ordered log entry, it uses the `value` field (acting as the request ID) from the leader's entry to match against its buffered raw payloads in `pendingRequests`.
    *   If a match is found, the Follower appends the full, structured log entry to its own log and removes the corresponding raw payload from its `pendingRequests`.

4.  **Payload Recovery:**
    *   A recovery mechanism (`RecoveryRequest`, `RecoveryResponse` messages and handlers) allows followers to fetch missing raw payloads (identified by their `Value`) from the leader if they were missed during the initial Switch dissemination.

### Key Change: Log Entry Structure (Alignment with Professor's Example)

Compared to the previous checkpoint (where log entries were `[term |-> T, value |-> V]`), the primary change in this version is the **modification of the Raft log entry structure to explicitly include a `payload` field**, as per the professor's example trace.

*   **Previous Log Entry Structure (in `LeaderOrderRequest`):**
    `entry == [term |-> entryTerm, value |-> v]`

*   **Current (New) Log Entry Structure (in `LeaderOrderRequest`):**
    `entry == [term |-> entryTerm, value |-> v, payload |-> v]`

    In this updated model:
    *   `term`: The term in which the leader ordered the entry.
    *   `value`: The original client request `v` (from the `Value` set), serving as the unique request identifier.
    *   `payload`: The original client request `v` (from the `Value` set), serving as the actual data/payload content.

**Impact of the Log Structure Change:**

1.  **`LeaderOrderRequest`:** Modified to create log entries with the `[term, value, payload]` structure.
2.  **`AppendEntries`:** Now implicitly sends these three-field records in the `mentries` field of `AppendEntriesRequest` messages, as it sources entries directly from the leader's log.
3.  **`HandleAppendEntriesRequest`:** Modified to correctly process incoming three-field records.
    *   When checking for existing entries, it compares `term` and `value` fields.
    *   When appending a new entry, it uses the `receivedEntry.value` (the ID part) to match against its `pendingRequests` (which still stores raw `Value`s) and then appends the full `receivedEntry` (`[term, value, payload]`) to its log.

This change ensures that the model's behavior, particularly the content of the replicated log and `AppendEntries` messages, aligns with the structure shown in the professor's example trace (e.g., `log = [ r1 |-> << [term |-> 2, value |-> "v1", payload |-> "v1"] >>, ...]`).

The core HovercRaft data flow (Client -> Switch -> Server Buffers -> Leader Orders -> Replication) remains consistent, with the main adaptation being this more explicit log entry format. The model has been successfully checked with TLC using `MySpec`, and the generated traces confirm this behavior.

## Project Update: HovercRaft TLA+ Model - [19/05/2025]

This commit finalizes the implementation of the HovercRaft protocol extensions to the base Raft TLA+ model. The model now strictly adheres to the requirement that leaders replicate only metadata references, with followers retrieving payloads from their local cache to construct full log entries. All core and bonus requirements have been addressed.

### Core HovercRaft Implementation ("Strict Metadata Replication"):

The model implements the following key aspects of HovercRaft:

1.  **Switch Component (`Switch` constant):**
    *   Clients send raw request payloads (`Value` `v`) to the Switch component (`SwitchClientRequest` action).
    *   The Switch buffers these raw payloads in `pendingRequests[Switch]`.
    *   The Switch disseminates these raw request payloads (`v`) to all Raft servers (Leader and Followers), populating their respective `pendingRequests` buffers (`SwitchDisseminate` action). This fulfills the requirement for simultaneous payload delivery to all nodes.

2.  **Leader-Driven Ordering & Metadata-Only Replication:**
    *   The Leader selects a raw payload `v` (which serves as both ID and payload content in this model) from its `pendingRequests` buffer.
    *   The Leader creates and stores a full log entry `[term |-> T, value |-> v, payload |-> v]` in its *local log*.
    *   **Crucially, when sending `AppendEntriesRequest` messages (`AppendEntries` action), the leader now sends only a metadata reference `[term |-> T, value |-> v]` in the `mentries` field. The `payload` field itself is not included in this replication message.** This strictly fulfills the requirement: "The leader node is only responsible for ordering requests by sending fixed-size metadata messages (referencing the client request) to followers, not the full request payload."

3.  **Follower Payload Caching, Matching, and Log Construction:**
    *   Followers temporarily store the unordered raw payloads (`v`) received via the Switch in their `pendingRequests[follower_id]` cache.
    *   When a Follower receives an `AppendEntriesRequest` containing the metadata reference `[term |-> T, value |-> v_id]` from the Leader:
        *   It uses `v_id` to check its `pendingRequests` cache.
        *   If the payload (`v_id`) is found in the cache, the Follower **retrieves** this payload and **constructs** the full log entry `[term |-> T, value |-> v_id, payload |-> retrieved_payload]` for its own log.
        *   The corresponding raw payload is then removed from `pendingRequests`.
    *   This fulfills the requirements: "Followers must temporarily store unordered client requests... and match them with the ordering metadata received from the leader," and aligns with the feedback "follower has some cache to check it and retrieve payload to be added to the log."

4.  **Bonus Requirement: Payload Recovery Mechanism:**
    *   A recovery mechanism (`RecoveryRequest`, `RecoveryResponse` messages and associated handler actions) is implemented.
    *   If a follower receives ordering metadata from the leader but finds the corresponding payload ID missing from its `pendingRequests` cache (simulating an unreliable multicast), it sends a `RecoveryRequest` for that payload ID to the leader.
    *   The leader, if it has the ordered entry, responds with the payload ID (which is the payload content in this model).
    *   The follower then adds the recovered payload ID to its `pendingRequests` cache, enabling it to process the entry on a subsequent `AppendEntries` attempt.
    *   This fulfills: "A recovery mechanism... must exist for followers to fetch missing client requests... from the leader..."

**Verification:**

The model has been successfully checked with TLC using the `MySpec` configuration. The generated traces confirm:
*   The Switch correctly disseminates raw payloads.
*   The leader's `AppendEntries` messages contain only `[term, value]` in the `mentries` field.
*   Followers correctly use their `pendingRequests` cache to find the payload and then construct and log the full `[term, value, payload]` entry.
*   The fundamental Raft safety invariants hold.

This implementation ensures a clear separation of payload delivery (via the Switch) and the leader's metadata-based ordering process, with followers actively using their cached payloads.

## Contributor
*   **ovidiu-cristian**
*   **Parsa**
