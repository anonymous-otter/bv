module SafetyProof {
  import opened CommonTypes

  import opened OpsStateMachine

  import opened Events

  datatype Variables = Variables(states: seq<OsmState>, events: seq<OsmEvent>, actions: seq<Option<OsmAction>>)

  // Check if the next state s' and the action a are the result of executing OSM with the current state s and event e
  ghost predicate OsmNext(s: OsmState, e: OsmEvent, s': OsmState, a: Option<OsmAction>) {
    var model := ExecuteOsmModel(s, e);
    model.state == s' && model.action == a
  }

  // Check if the state machine is well-formed
  // 1. The number of states is equal to the number of events + 1
  // 2. The number of states is equal to the number of actions + 1
  // 3. Every event is valid trigger for the state machine
  ghost predicate WF(v: Variables)
  {
    && |v.states| == |v.events| + 1
    && |v.states| == |v.actions| + 1
    && forall i :: 0 <= i < |v.events| ==> OsmNext(v.states[i], v.events[i], v.states[i + 1], v.actions[i])
  }

  // Check if the state machine is in the initial state
  ghost predicate Init(v: Variables) {
    && |v.states| == 1
    && |v.events| == 0
    && |v.actions| == 0
    && v.states[0] == Created
  }

  // Check if the state machine can transition from state v to state v'
  ghost predicate Next(v: Variables, v': Variables)
    requires WF(v)
  {
    && |v.states| + 1 == |v'.states|
    && |v.events| + 1 == |v'.events|
    && |v.actions| + 1 == |v'.actions|
    && v'.states[..|v'.states| - 1] == v.states
    && v'.events[..|v'.events| - 1] == v.events
    && v'.actions[..|v'.actions| - 1] == v.actions
    && OsmNext(v.states[|v.states| - 1], v'.events[|v'.events| - 1], v'.states[|v'.states| - 1], v'.actions[|v'.actions| - 1])
  }

  /**
    * Safety properties
    */

  // Safety property 1: If the state machine is in the Destroyed state, it remains destroyed.
  ghost predicate SafetyP1(v: Variables)
    requires WF(v)
  {
    forall i ::
      (
        && 0 <= i < |v.states|
        && v.states[i] == Destroyed
      )
      ==> forall j: nat :: i <= j < |v.states| ==> v.states[j] == Destroyed

  }

  // Safety property 2: If the state machine receives error events, the state machine enters the Destroyed state.
  ghost predicate SafetyP2(v: Variables)
    requires WF(v)
  {
    forall i ::
      (
        && 0 <= i < |v.events|
        && IsErrorEvent(v.states[i], v.events[i])
      )
      ==> v.states[i + 1] == Destroyed
  }

  // Safety property 3: If the state machine receives unmodeled events, it remains in the same state and performs no action.
  ghost predicate SafetyP3(v: Variables)
    requires WF(v)
  {
    forall i ::
      (
        && 0 <= i < |v.events|
        && !IsModeledEvent(v.states[i], v.events[i])
      )
      ==> v.states[i + 1] == v.states[i] && v.actions[i] == None
  }

  // Check if the input state machine satisfies the safety properties
  ghost predicate Safety(v: Variables)
  {
    && WF(v)
    && SafetyP1(v)
    && SafetyP2(v)
    && SafetyP3(v)
  }

  /**
    * Safety proof by induction
    */

  // Lemma to prove the Initiation step
  lemma SafetyInit(v: Variables)
    requires Init(v)
    ensures Safety(v)
  {}

  // Lemma to prove the Preservation step
  lemma SafetyNext(v: Variables, v': Variables)
    requires Safety(v)
    requires Next(v, v')
    ensures Safety(v')
  {}
}
