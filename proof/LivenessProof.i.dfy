module LivenessProof {
  import opened OpsStateMachine

  /**
    * Liveness
    */
  // Check if the state machine is in the initial state
  ghost predicate Init(s: OsmState) {
    s == Created
  }

  // Check if the state machine can transition from state s to state s'
  ghost predicate Next(s: OsmState, s': OsmState) {
    exists e: OsmEvent :: ExecuteOsmModel(s, e).state == s'
  }

  // Data type representing a trace of state machine transitions.
  type Trace = nat -> OsmState

  // The trigger function to help with the verification in Dafny
  ghost function Identity(i: nat): nat {
    i
  }

  // Fairness: the state machine cannot stay in the same state forever except for Destroyed
  // i.e. the state machine can always reach a next state other than the current state unless it is in Destroyed state
  ghost predicate Fairness(trace: Trace) {
    forall i: nat {:trigger Identity(i)} ::
      (
        trace(i) != Destroyed
        ==> exists j: nat ::
            (
              && j > i
              && (forall k: nat :: i < k < j ==> trace(k) == trace(i))
              && trace(j) != trace(i)
              && Next(trace(j - 1), trace(j))
            )
      )
  }

  // Check if a trace is fair:
  // 1. The first state is the initial state
  // 2. Every two consecutive states is a valid transition
  // 3. Fairness is satisfied
  ghost predicate IsFairTrace(trace: Trace) {
    && Init(trace(0))
    && (forall i: nat :: Next(trace(i), trace(i + 1)))
    && Fairness(trace)
  }

  // A helper lemma to find the next state in a trace that is different from the current state (not Open or Destroyed)
  // and satisfies the Next predicate
  lemma NextHelper(trace: Trace, n: nat) returns (n': nat)
    requires IsFairTrace(trace)
    requires trace(n) != Open && trace(n) != Destroyed
    ensures n' > n && trace(n') != trace(n) && Next(trace(n), trace(n'))
  {
    assert exists n': nat :: n' > n && trace(n') != trace(n) && Next(trace(n), trace(n')) by {
      assert Identity(n) == n;
    }
    n' :| n' > n && trace(n') != trace(n) && Next(trace(n), trace(n'));
  }

  // Lemma to prove liveness: given a fair trace, the state machine will eventually reach either Open or Destroyed state
  lemma Eventually(trace: Trace)
    requires IsFairTrace(trace)
    ensures exists n: nat :: trace(n) == Open || trace(n) == Destroyed
  {
    var n := 0;

    var n' := NextHelper(trace, n);
    assert trace(n') == InitiatorWaitSecurityCheck || trace(n') == AcceptorWaitSecurityCheck || trace(n') == WaitPeerConnectResponse || trace(n') == Destroyed;
    n := n';

    if (trace(n) == InitiatorWaitSecurityCheck) {
      n' := NextHelper(trace, n);
      assert trace(n') == WaitPeerConnectResponse || trace(n') == Destroyed;
      n := n';
    }

    if (trace(n) == AcceptorWaitSecurityCheck) {
      n' := NextHelper(trace, n);
      assert trace(n') == WaitLocalConnectResponse || trace(n') == Config || trace(n') == Open || trace(n') == Destroyed;
      n := n';
    }

    if (trace(n) == WaitLocalConnectResponse) {
      n' := NextHelper(trace, n);
      assert trace(n') == Config || trace(n') == Open || trace(n') == WaitPeerDisconnectResponse || trace(n') == Destroyed;
      n := n';
    }

    if (trace(n) == WaitPeerConnectResponse) {
      n' := NextHelper(trace, n);
      assert trace(n') == Config || trace(n') == Open || trace(n') == WaitPeerDisconnectResponse || trace(n') == Destroyed;
      n := n';
    }

    if (trace(n) == Config) {
      n' := NextHelper(trace ,n);
      assert trace(n') == Open || trace(n') == WaitPeerDisconnectResponse || trace(n') == WaitLocalDisconnectResponse || trace(n') == Destroyed;
      n := n';
    }

    if (trace(n) == WaitPeerDisconnectResponse || trace(n) == WaitLocalDisconnectResponse) {
      n' := NextHelper(trace, n);
      assert trace(n') == Destroyed;
    }
  }
}
