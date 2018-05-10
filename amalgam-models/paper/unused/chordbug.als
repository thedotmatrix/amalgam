/* ========================================================================
A MODEL OF THE FULL CHORD ROUTING PROTOCOL IN ALLOY
   Pamela Zave, 15 June 2010
      Copyright AT&T Labs, Inc., 2009, 2010, 2011, 2012.
======================================================================== */

open util/ordering[Time] as trace
open util/ordering[Node] as ring

/* ========================================================================
TEMPORAL STRUCTURE
   Note that if time has a scope of x, there will be exactly x times, not
   x or fewer.  However, there need not be x-1 real events, because Null
   events will take up the slack.
======================================================================== */

sig Time { }

abstract sig Event {
   pre:  Time,
   post: Time,
   cause: lone (Event - Null)
}

sig Null extends Event { } { no cause }

fact TemporalStructure {
   all t: Time - trace/last | one e: Event | e.pre = t 
   all t: trace/last | no  e: Event | e.pre = t 
   all e: Event | e.post = (e.pre).next  
}

fact CauseHasSingleEffect { cause in Event lone -> Event }

fact CausePrecedesEffect { 
   all e1, e2: Event | e1 = e2.cause => lt[e1.pre,e2.pre]  }

/* ========================================================================
STRUCTURE OF A RING NETWORK
   Simplifications:
   1) In this model, the node itself, its IP address, and its hashed 
      identifier are all conflated.
   2) The successor list of a node has size 2.  This brevity does not
      eliminate any interesting behaviors.
   3) Fingers are not included in this model, as they have no effect on
      ring structure, and the early fingers and successors coincide.
======================================================================== */

sig Node {
   succ: Node lone -> Time,
   succ2: Node lone -> Time,
   prdc: Node lone -> Time,
   bestSucc: Node lone -> Time }
{  
-- This defines bestSucc.
   all t: Time |
      (Member[succ.t,t] && Member[succ2.t,t] => bestSucc.t = succ.t)
   && (Member[succ.t,t] && NonMember[succ2.t,t] => bestSucc.t = succ.t)
   && (NonMember[succ.t,t] && Member[succ2.t,t] => bestSucc.t = succ2.t)
   && (NonMember[succ.t,t] && NonMember[succ2.t,t] => no bestSucc.t)

-- A node is unambiguously a member or not.
   all t: Time | Member[this,t] || NonMember[this,t]  
}

pred Member [n: Node, t: Time] {  some n.succ.t  }
pred NonMember [n: Node, t: Time] {  
   no n.succ.t && no n.prdc.t && no n.succ2.t  }

pred Between [n1, n2, n3: Node] {
   lt[n1,n3] =>   ( lt[n1,n2] && lt[n2,n3] )
             else ( lt[n1,n2] || lt[n2,n3] )  }
                                       -- for all x and y,   Between{x,y,x]
                                             -- for all x, ! Between{x,x,x]
                                       -- for all x and y, ! Between{x,x,y]
                                       -- for all x and y, ! Between{y,x,x]

/* ========================================================================
CANDIDATE INVARIANT PROPERTIES
======================================================================== */

pred OneOrderedRing [t: Time] {
   let ringMembers = { n: Node | n in n.(^(bestSucc.t)) } |
      some ringMembers                                 -- at least one ring
   && (all disj n1, n2: ringMembers | n1 in n2.(^(bestSucc.t)) ) -- not two
   && (all disj n1, n2, n3: ringMembers |               -- ring is globally
         n2 = n1.bestSucc.t => ! Between[n1,n3,n2]      -- ordered
      )
}

pred ConnectedAppendages [t: Time] { 
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: members | n in n.(^(bestSucc.t)) } |
      all na: members - ringMembers |                           -- na is in
         some nc: ringMembers | nc in na.(^(bestSucc.t))    -- an appendage
                                                        -- yet reaches ring
}

pred AntecedentPredecessors [t: Time] {
   all n: Node | let antes = (succ.t).n | 
      Member[n.prdc.t,t] => n.prdc.t in antes
}  

pred OrderedAppendages [t: Time] {
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: members | n in n.(^(bestSucc.t)) } |
   let appendSucc = bestSucc.t - (ringMembers -> Node) |
      all n: ringMembers |
         all disj a1, a2, a3: (members - ringMembers) + n |
            (  n in a1.(^appendSucc)
            && a2 = a1.appendSucc
            && (a1 in a3.(^appendSucc) || a3 in a2.(^appendSucc) )
            )  => ! Between[a1,a3,a2]
}

pred OrderedMerges [t: Time] {
   let ringMembers = { n: Node | n in n.(^(succ.t)) } |
      all disj n1, n2, n3: Node |
         (  n3 in n1.bestSucc.t
         && n3 in n2.bestSucc.t
         && n1 in ringMembers 
         && n2 !in ringMembers
         && n3 in ringMembers 
         ) => Between[n1,n2,n3]
}

pred DistinctSuccessors [t: Time] {
   let members = { n: Node | Member[n,t] } |
      let ringMembers = { n: members | n in n.(^(succ.t)) } |
         all n: members |
         (  (n.succ2.t = n.succ.t => 
                                (# ringMembers  = 1 && n in ringMembers))
         && (n.succ2.t = n        => 
                                (# ringMembers <= 2 && n in ringMembers))
         )
}

pred OrderedSuccessors [t: Time] {
   let members = { n: Node | Member[n,t] } |
      let ringMembers = { n: members | n in n.(^(succ.t)) } |
         all n: members | 
            some n.succ2.t => 
            (  Between[n,n.succ.t,n.succ2.t] || n = ringMembers  )
}

pred ValidSuccessorList [t: Time] { 
   let members = { n: Node | Member[n,t] } |
   all disj n, m: members | 
      let antes = (succ.t).n |
         Between[n.succ.t,m,n.succ2.t]
                                  -- n's successors skip over a live node m
         => m !in antes.succ2.t
                          -- m is not in successor list of any n antecedent
}  

pred ReachableSuccessor2 [t: Time] {
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: Node | n in n.(^(bestSucc.t)) } |
   (  (all n: members - ringMembers | 
         Member[n.succ2.t,t] => n.succ2.t in n.(^(bestSucc.t))
      )
   && (all n: ringMembers | 
         Member[n.succ2.t,t] 
      => (  n.succ2.t in ringMembers
         || (  let altSucc = bestSucc.t + n->n.succ2.t - n->n.succ.t |
               let altRingMembers = { a: Node | a in n.(^(altSucc)) } |
                  all disj a1, a2, a3: altRingMembers |  
                     a2 = a1.altSucc => ! Between[a1,a3,a2]  
            )
         )
      )
   )
}

pred AvengerInvariant [t: Time] {
   let members = { n: Node | Member[n,t] } |
      all n: members | 
         Member[n.prdc.t,t] => ! Between[n.prdc.t,n.bestSucc.t,n]
}

pred Valid [t: Time] { 
      OneOrderedRing[t]                          -- from PODC Full, revised
   && ConnectedAppendages[t]                     -- from PODC Full, revised
   && AntecedentPredecessors[t]                                      -- new
   && OrderedAppendages[t]                                -- from PODC Full
   && OrderedMerges[t]                                    -- from PODC Full
   && DistinctSuccessors[t]                                          -- new
   && OrderedSuccessors[t]                                           -- new
   && ValidSuccessorList[t]                      -- from PODC Full, revised
   && ReachableSuccessor2[t]                                         -- new
}

-- These are the only properties needed for an undisturbed network to
-- become ideal through stabilization and reconciliation.
pred CoreValid [t: Time] { 
      OneOrderedRing[t]       
   && ConnectedAppendages[t] 
}

pred SomeBestSuccessor [t: Time] { 
   all n: Node | Member[n,t] => some n.bestSucc.t  }

assert ValidImpliesSomeBestSuccessor {
   all t: Time | Valid[t] => SomeBestSuccessor[t] }
check ValidImpliesSomeBestSuccessor for 7 but 0 Event, 1 Time

/* ========================================================================
IDEAL PROPERTIES
======================================================================== */

pred Stable [t: Time] { let members = { n: Node | Member[n,t] } |
   all n1, n2: members | n2 = n1.succ.t <=> n1 = n2.prdc.t
}

pred AllRing [t: Time] { let members = { n: Node | some n.succ.t } |
   all n1, n2: members | n2 in n1.(^(succ.t))
}

pred Reconciled [t: Time] { let members = { n: Node | Member[n,t] } |
   all n: members | 
         Member[n.succ.t,t] 
      && Member[n.succ2.t,t]
      && n.succ2.t = (n.succ.t).succ.t
}

pred Succ2Correctness [t: Time] { let members = { n: Node | Member[n,t] } |
   all n: members |
      (Member[n.succ2.t,t] && n.succ2.t != n.bestSucc.t)
   => n.succ2.t = (n.bestSucc.t).bestSucc.t
}

pred Ideal [t: Time] {  
      Valid[t] 
   && Stable[t]                                  -- from PODC Full, revised
   && Reconciled[t]                              -- from PODC Full, revised
}

assert IdealImpliesAllRing { all t: Time | Ideal[t] => AllRing[t] }
check IdealImpliesAllRing for 7 but 0 Event, 1 Time

assert IdealImpliesSucc2Correct { all t: Time | 
   Ideal[t] => Succ2Correctness[t] }
check IdealImpliesSucc2Correct for 7 but 0 Event, 1 Time

/* ========================================================================
SPECIFICATION OF EVENTS

   Chord assumes that a node's successor list is long enough so that
   the probability of all of its successor's being dead is extremely 
   low.  In Alloy this assumption is encoded deterministically.  The
   specification of the Fail event will not allow a node to fail if it
   would leave another node with no live node in its successor list.

   Straightforward bug fixes:
   1) The Join specification checks that the successor adopted by the
      joining node is live.  Otherwise the join will not actually connect
      the joining node to the network.
   2) The Stabilize specification checks that the successor adopted by the
      stabilizing node is live.  Otherwise the ring can be lost easily.
   These bugs were found during analysis.  They are fixed so that analysis
   can find other problems.
======================================================================== */

abstract sig RingEvent extends Event { node: Node }
sig Join extends RingEvent { } { no cause }
sig Stabilize extends RingEvent { } { no cause  }
sig Notified extends RingEvent { newPrdc: Node } { some cause }
sig Fail extends RingEvent { } { no cause }
sig Flush extends RingEvent { } { no cause }
sig Update extends RingEvent { } { no cause }
sig Reconcile extends RingEvent { } { no cause }

fact NonMemberCanJoin {
   all j: Join, n: j.node, t: j.pre | {
      NonMember[n,t]
      (some m: Node |    Member[m,t]
                      && Between[m,n,m.succ.t]
                      && Member[m.succ.t,t]
                      && n.succ.(j.post) = m.succ.t
      )
      no n.prdc.(j.post)
      no cause:>j
}  }

fact StabilizeMayChangeSuccessor {
   all s: Stabilize, n: s.node, t: s.pre |
   let newSucc = (n.succ.t).prdc.t       | {
      Member[n,t]
      Member[n.succ.t,t]
      (  (  some newSucc
         && Between[n,newSucc,n.succ.t]
         && Member[newSucc,t]
         )
         -- accept new successor or not
         => n.succ.(s.post) = newSucc else n.succ.(s.post) = n.succ.t
      )
      (some f: Notified |   f.cause = s
                       && f.node = n.succ.(s.post)
                       && f.newPrdc = n
      )
}  }

fact NotifiedMayChangePredecessor {
   all f: Notified, n: f.node, p: f.newPrdc, t: f.pre |
      (   Member[n,t]
      && (no n.prdc.t || Between[n.prdc.t,p,n])
      )
   -- accept new predecessor
      =>   (n.prdc.(f.post) = p && no cause:>f)
   -- else do nothing
      else (n.prdc.(f.post) = n.prdc.t && no cause:>f)
}

fact MemberCanFail {
   all f: Fail, n: f.node, t: f.pre | {
      Member[n,t]
      (all m: Node | m.succ.t = n => Member[m.succ2.t,t])
      (all m: Node | m.succ2.t = n => Member[m.succ.t,t])
      n.succ.t != n.succ2.t
      NonMember[n,f.post] 
      no cause:>f
}  }

fact FlushMayChangePredecessor {
   all f: Flush, n: f.node, t: f.pre | {
      (Member[n,t] && NonMember[n.prdc.t,t])
         =>   no n.prdc.(f.post) 
         else n.prdc.(f.post) = n.prdc.t
      no cause:>f
}  }

fact UpdateMayChangeSuccessor {
   all u: Update, n: u.node, t: u.pre |
      let oldSucc = n.succ.t |  
      let oldSucc2 = n.succ2.t | {
         (Member[n,t] && NonMember[oldSucc,t] && some oldSucc2)
         =>   (  n.succ.(u.post) = oldSucc2
              && no n.succ2.(u.post)
              )
         else (n.succ.(u.post) = oldSucc && n.succ2.(u.post) = oldSucc2)
                               --  at least one of the two must be a member
      no cause:>u
}  }

fact ReconcileMayChangeSuccessor2 {
   all r: Reconcile, n: r.node, t: r.pre |
      let oldSucc2 = n.succ2.t      | 
      let newSucc2 = (n.succ.t).succ.t | {      -- not necessarily a member
         (  Member[n,t] 
         && Member[n.succ.t,t]
         && newSucc2 != oldSucc2                   -- this must be a change
         && (newSucc2 = n.succ.t =>           -- this must not be redundant
                 n.succ.t = n)                  
         )  =>   n.succ2.(r.post) = newSucc2
            else n.succ2.(r.post) = oldSucc2
         no cause:>r
}  }

/* ========================================================================
FRAME CONDITIONS
   Frame conditions say, "and nothing else changes."
======================================================================== */

fact SuccessorFieldFrameCondition {
   all e: Event, n: Node | n.succ.(e.pre) != n.succ.(e.post)
   => (  (e in Join && e.node = n)
      || (e in Stabilize && e.node = n)
      || (e in Fail && e.node = n)
      || (e in Update && e.node = n)
      )
}

fact Successor2FieldFrameCondition {
   all e: Event, n: Node | n.succ2.(e.pre) != n.succ2.(e.post)
   => (  (e in Fail && e.node = n)
      || (e in Update && e.node = n)
      || (e in Reconcile && e.node = n)
      )
}

fact PredecessorFieldFrameCondition {
   all e: Event, n: Node | n.prdc.(e.pre) != n.prdc.(e.post)
   => (  (e in Notified && e.node = n)
      || (e in Fail && e.node = n)
      || (e in Flush && e.node = n)
      )
}

/* ========================================================================
CHANGE PREDICATES
   Change predicates identify states in which, if an event occurs, it will
   change the state.
======================================================================== */

pred StabilizationWillChangeSuccessor [n, nSucc: Node, t: Time] {
   let newSucc = (n.succ.t).prdc.t |
         Member[n,t]
      && some newSucc
      && Between[n,newSucc,n.succ.t]
      && Member[newSucc,t]
      && nSucc = newSucc
}

pred StabilizationShouldChangePredecessor [n, nSucc: Node, t: Time] {
   (  (  StabilizationWillChangeSuccessor[n,nSucc,t]
      || (nSucc = n.succ.t && Member[n,t] && Member[nSucc,t])
      )
   && (  no nSucc.prdc.t 
      || (some nSucc.prdc.t && Between[nSucc.prdc.t,n,nSucc])
      )
   )
}

pred ReconciliationWillFlushPredecessor [n: Node, t: Time] {
   Member[n,t] && some n.prdc.t && NonMember[n.prdc.t,t] }

pred ReconciliationWillChangeSuccessor [n, nSucc: Node, t: Time] {
      Member[n,t] && NonMember[n.succ.t,t] 
   && some n.succ2.t && nSucc = n.succ2.t }

pred ReconciliationWillChangeSuccessor2 [n, nSucc2: Node, t: Time] {
   let oldSucc2 = n.succ2.t |
   let newSucc2 = (n.succ.t).succ.t | 
         Member[n,t] 
      && Member[n.succ.t,t]
      && nSucc2 = newSucc2
      && newSucc2 != oldSucc2
      && (newSucc2 = n.succ.t => n.succ.t = n)                  
}

/* ========================================================================
LIVENESS VERIFICATION
======================================================================== */

assert ValidRingIsImprovable {
   (  CoreValid[trace/first] && ! Ideal[trace/first]  ) 
   =>
   (  (some n1, n2: Node | 
         StabilizationWillChangeSuccessor[n1,n2,trace/first])
   || (some n1, n2: Node | 
         StabilizationShouldChangePredecessor[n1,n2,trace/first])
   || (some n: Node | ReconciliationWillFlushPredecessor[n,trace/first])
   || (some n1, n2: Node | 
         ReconciliationWillChangeSuccessor[n1,n2,trace/first])
   || (some n1, n2: Node | 
         ReconciliationWillChangeSuccessor2[n1,n2,trace/first])
   )
}
check ValidRingIsImprovable for 5 but 0 Event, 1 Time 
check ValidRingIsImprovable for 7 but 0 Event, 1 Time 

assert IdealRingCannotImprove {
   Ideal[trace/first]
   =>
   (  (no n1, n2: Node | 
         StabilizationWillChangeSuccessor[n1,n2,trace/first])
   && (no n1, n2: Node | 
         StabilizationShouldChangePredecessor[n1,n2,trace/first])
   && (no n: Node | ReconciliationWillFlushPredecessor[n,trace/first])
   && (no n1, n2: Node | 
         ReconciliationWillChangeSuccessor[n1,n2,trace/first])
   && (no n1, n2: Node | 
         ReconciliationWillChangeSuccessor2[n1,n2,trace/first])
   )
}
check IdealRingCannotImprove for 5 but 0 Event, 1 Time 
check IdealRingCannotImprove for 7 but 0 Event, 1 Time 

/* ========================================================================
SAFETY VERIFICATION OF INITIALIZATION AND SINGLE OPERATIONS
   This verification cannot be completed because there is no invariant
   strong enough to imply CoreValid.  These safety checks use a weak form
   of the desired invariant that can be changed easily here.  By
   experimenting, we try to find as many fixable problems as possible.
======================================================================== */

assert InitialIsValid { 
   let members = { n: Node | Member[n,trace/first] } |
   (  one members 
   && members.succ.trace/first = members
   && no members.prdc.trace/first 
   && no members.succ2.trace/first
   ) => Valid[trace/first]
}
check InitialIsValid for 1 but 0 Event, 1 Time

assert JoinPreservesValidity {
   some Join && Valid[trace/first] => WeakJValid[trace/last] }
check JoinPreservesValidity for 3 but 1 Event, 2 Time
check JoinPreservesValidity for 4 but 1 Event, 2 Time
check JoinPreservesValidity for 5 but 1 Event, 2 Time 

pred WeakJValid [t: Time] { 
      OneOrderedRing[t]                       
   && ConnectedAppendages[t]               
-- && AntecedentPredecessors[t]    
-- && OrderedAppendages[t]        
-- && OrderedMerges[t]           
   && DistinctSuccessors[t]           
   && OrderedSuccessors[t]         
-- && ValidSuccessorList[t]     
-- && ReachableSuccessor2[t]  
}

assert StabilizationPreservesValidity {
   some Stabilize && Valid[trace/first] => WeakSValid[trace/last] }
check StabilizationPreservesValidity for 3 but 2 Event, 3 Time--    1587 ms
check StabilizationPreservesValidity for 4 but 2 Event, 3 Time--   19853 ms
check StabilizationPreservesValidity for 5 but 2 Event, 3 Time--  362522 ms

pred WeakSValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
   && OrderedAppendages[t]             
-- && OrderedMerges[t]              
-- && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
   && ReachableSuccessor2[t]  
-- && ValidSuccessorList[t]    
}

assert FailPreservesValidity {
   some Fail && Valid[trace/first] => WeakFValid[trace/last] }
check FailPreservesValidity for 3 but 1 Event, 2 Time
check FailPreservesValidity for 4 but 1 Event, 2 Time
check FailPreservesValidity for 5 but 1 Event, 2 Time 

pred WeakFValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
-- && OrderedMerges[t]              
-- && OrderedAppendages[t]             
-- && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
   && ValidSuccessorList[t]    
-- && ReachableSuccessor2[t]  
}

assert FlushPreservesValidity {
   some Flush && Valid[trace/first] => Valid[trace/last] }
check FlushPreservesValidity for 3 but 1 Event, 2 Time
check FlushPreservesValidity for 4 but 1 Event, 2 Time
check FlushPreservesValidity for 5 but 1 Event, 2 Time 

assert UpdatePreservesValidity { 
   some Update && Valid[trace/first] => Valid[trace/last]  }
check UpdatePreservesValidity for 3 but 1 Event, 2 Time
check UpdatePreservesValidity for 4 but 1 Event, 2 Time
check UpdatePreservesValidity for 5 but 1 Event, 2 Time

assert ReconcilePreservesValidity { 
   some Reconcile && Valid[trace/first] => WeakRValid[trace/last]  }
check ReconcilePreservesValidity for 3 but 1 Event, 2 Time
check ReconcilePreservesValidity for 4 but 1 Event, 2 Time
check ReconcilePreservesValidity for 5 but 1 Event, 2 Time 

pred WeakRValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
   && OrderedAppendages[t]             
   && OrderedMerges[t]              
   && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
-- && ValidSuccessorList[t]    
   && ReachableSuccessor2[t]  
}

/* ========================================================================
VALIDATION OF COUNTEREXAMPLES: all checked previously

pred CounterOrderedMerges {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8, e9, e10, e11, e12: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   e8.post = e9.pre
   e9.post = e10.pre
   e10.post = e11.pre
   e11.post = e12.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n3
   e1 in Stabilize && e1.node = n3 
   e2 in Notified && e2.node = n0
   e3 in Stabilize && e3.node = n0
   e4 in Notified && e4.node = n3                         -- ring of size 2
   e5 in Join && e5.node = n1
   e6 in Join && e6.node = n2
   e7 in Stabilize && e7.node = n1
   e8 in Notified && e8.node = n3         -- up to first snapshot of figure
   e9 in Stabilize && e9.node = n2
   e10 in Notified && e10.node = n3       -- second
   e11 in Stabilize && e11.node = n0
   e12 in Notified && e12.node = n2       -- third
} }
run CounterOrderedMerges for 1 but 4 Node, 13 Event, 14 Time

pred CounterOrderedAppendages {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
             e17, e18: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   e8.post = e9.pre
   e9.post = e10.pre
   e10.post = e11.pre
   e11.post = e12.pre
   e12.post = e13.pre
   e13.post = e14.pre
   e14.post = e15.pre
   e15.post = e16.pre
   e16.post = e17.pre
   e17.post = e18.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n1
   e1 in Join && e1.node = n2 
   e2 in Join && e2.node = n3
   e3 in Stabilize && e3.node = n2
   e4 in Notified && e4.node = n0         -- up to first snapshot of figure
   e5 in Stabilize && e5.node = n0
   e6 in Notified && e6.node = n2   
   e7 in Stabilize && e7.node = n3
   e8 in Notified && e8.node = n0         -- second
   e9 in Stabilize && e9.node = n1
   e10 in Notified && e10.node = n3
   e11 in Reconcile && e11.node = n2
   e12 in Reconcile && e12.node = n3      -- third
   e13 in Fail && e13.node = n0 
   e14 in Update && e14.node = n2
   e15 in Update && e15.node = n3 
   e16 in Flush && e16.node = n3      
   e17 in Stabilize && e17.node = n3
   e18 in Notified && e18.node = n2       -- fourth
} }
run CounterOrderedAppendages for 1 but 4 Node, 19 Event, 20 Time

pred CounterValidSuccessorList {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
             e17, e18: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   e8.post = e9.pre
   e9.post = e10.pre
   e10.post = e11.pre
   e11.post = e12.pre
   e12.post = e13.pre
   e13.post = e14.pre
   e14.post = e15.pre
   e15.post = e16.pre
   e16.post = e17.pre
   e17.post = e18.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n2
   e1 in Stabilize && e1.node = n2 
   e2 in Notified && e2.node = n0
   e3 in Stabilize && e3.node = n0
   e4 in Notified && e4.node = n2                         -- ring of size 2
   e5 in Join && e5.node = n1
   e6 in Reconcile && e6.node = n1        -- up to first snapshot of figure
   e7 in Join && e7.node = n3
   e8 in Stabilize && e8.node = n3 
   e9 in Notified && e9.node = n0
   e10 in Stabilize && e10.node = n2
   e11 in Notified && e11.node = n3    
   e12 in Reconcile && e12.node = n0      -- second
   e13 in Stabilize && e13.node = n1 
   e14 in Notified && e14.node = n2
   e15 in Stabilize && e15.node = n0 
   e16 in Notified && e16.node = n1       -- third
   e17 in Fail && e17.node = n2
   e18 in Update && e18.node = n1         -- fourth
} }
run CounterValidSuccessorList for 1 but 4 Node, 19 Event, 20 Time

pred CounterConnectedAppendages {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n2
   e1 in Stabilize && e1.node = n2 
   e2 in Notified && e2.node = n0
   e3 in Stabilize && e3.node = n0
   e4 in Notified && e4.node = n2
   e5 in Reconcile && e5.node = n0    -- first
   e6 in Fail && e6.node = n2         -- second
   e7 in Join && e7.node = n1
   e8 in Update && e8.node = n0       -- third
} }
run CounterConnectedAppendages for 1 but 4 Node, 9 Event, 10 Time
-- Can only be instantiated with the bug fix in Join removed.

pred CounterAtLeastOneRing {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8, e9, e10, e11: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   e8.post = e9.pre
   e9.post = e10.pre
   e10.post = e11.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n2
   e1 in Stabilize && e1.node = n2 
   e2 in Notified && e2.node = n0
   e3 in Stabilize && e3.node = n0
   e4 in Notified && e4.node = n2                         -- ring of size 2
   e5 in Join && e5.node = n1
   e6 in Stabilize && e6.node = n1
   e7 in Notified && e7.node = n2         -- up to first snapshot of figure
   e8 in Fail && e8.node = n1             -- second
   e9 in Stabilize && e9.node = n0
   e10 in Notified && e10.node = n1
   e11 in Flush && e11.node = n2          -- third
} }
run CounterAtLeastOneRing for 1 but 4 Node, 12 Event, 13 Time
-- Can only be instantiated with the bug fix in Stabilize removed.

pred CounterAtMostOneRing {
   some disj n0, n1, n2, n3: Node,
        disj e0, e1, e2, e3, e4, e5, e6,
             e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
             e17, e18, e19, e20: Event | {
   lt[n0,n1] && lt[n1,n2] && lt[n2,n3]
   e0.post = e1.pre
   e1.post = e2.pre
   e2.post = e3.pre
   e3.post = e4.pre
   e4.post = e5.pre
   e5.post = e6.pre
   e6.post = e7.pre
   e7.post = e8.pre
   e8.post = e9.pre
   e9.post = e10.pre
   e10.post = e11.pre
   e11.post = e12.pre
   e12.post = e13.pre
   e13.post = e14.pre
   e14.post = e15.pre
   e15.post = e16.pre
   e16.post = e17.pre
   e17.post = e18.pre
   e18.post = e19.pre
   e19.post = e20.pre
   (let members0 = { n: Node | Member[n,trace/first] } | members0 = n0 
      && no members0.prdc.trace/first && no members0.succ2.trace/first )
   e0 in Join && e0.node = n2
   e1 in Stabilize && e1.node = n2 
   e2 in Notified && e2.node = n0
   e3 in Stabilize && e3.node = n0
   e4 in Notified && e4.node = n2
   e5 in Reconcile && e5.node = n0
   e6 in Reconcile && e6.node = n2        -- up to first snapshot of figure
   e7 in Join && e7.node = n1
   e8 in Stabilize && e8.node = n1 
   e9 in Notified && e9.node = n2
   e10 in Stabilize && e10.node = n0
   e11 in Notified && e11.node = n1
   e12 in Join && e12.node = n3
   e13 in Stabilize && e13.node = n3 
   e14 in Notified && e14.node = n0
   e15 in Stabilize && e15.node = n2 
   e16 in Notified && e16.node = n3      -- up to second snapshot of figure
   e17 in Fail && e17.node = n1
   e18 in Fail && e18.node = n3
   e19 in Update && e19.node = n0
   e20 in Update && e20.node = n2                -- last snapshot of figure
} }
run CounterAtMostOneRing for 1 but 4 Node, 21 Event, 22 Time

-- The counterexample to OrderedRing is very similar, and is not modeled.
======================================================================== */

/* ========================================================================
VALIDATION OF CHANGE PREDICATES: all checked previously

assert SSChangeWorksSequentially {
   all n, nSucc: Node |
   (  Valid[trace/first]
   && StabilizationWillChangeSuccessor[n,nSucc,trace/first]
   && (some s: Stabilize | s.node = n)
   )
   => n.succ.trace/last = nSucc
}
check SSChangeWorksSequentially for 5 but 1 Event, 2 Time 

assert SPChangeWorksSequentially {
   all n, nSucc: Node |
   (  Valid[trace/first]
   && StabilizationShouldChangePredecessor[n,nSucc,trace/first]
   && (some s: Stabilize | s.node = n)
   )
   => nSucc.prdc.trace/last = n
}
check SPChangeWorksSequentially for 5 but 2 Event, 3 Time 

assert RPChangeWorksSequentially {
   all n: Node |
   (  Valid[trace/first]
   && ReconciliationWillFlushPredecessor[n,trace/first]
   && (some f: Flush | f.node = n)
   )
   => no n.prdc.trace/last
}
check RPChangeWorksSequentially for 5 but 1 Event, 2 Time 

assert RSChangeWorksSequentially {
   all n, nSucc: Node |
   (  Valid[trace/first]
   && ReconciliationWillChangeSuccessor[n,nSucc,trace/first]
   && (some u: Update | u.node = n)
   )
   => n.succ.trace/last = nSucc
}
check RSChangeWorksSequentially for 5 but 1 Event, 2 Time 

assert RS2ChangeWorksSequentially {
   all n, nSucc2: Node |
   (  Valid[trace/first]
   && ReconciliationWillChangeSuccessor2[n,nSucc2,trace/first]
   && (some r: Reconcile | r.node = n)
   )
   => n.succ2.trace/last = nSucc2
}
check RS2ChangeWorksSequentially for 5 but 1 Event, 2 Time 
======================================================================== */

/* ========================================================================
VALIDATION OF RING STRUCTURE: all checked previously

pred NotOneOrderedRing [t: Time] { 
      ! OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run NotOneOrderedRing for 2 but 0 Event, 1 Time

pred DisconnectedAppendage [t: Time] { 
      OneOrderedRing[t]    
   && ! ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run DisconnectedAppendage for 3 but 0 Event, 1 Time

pred NonAntecedentPredecessor [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && ! AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run NonAntecedentPredecessor for 2 but 0 Event, 1 Time

pred DisorderedAppendage [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && ! OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run DisorderedAppendage for 3 but 0 Event, 1 Time

pred DisorderedMerge [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && ! OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run DisorderedMerge for 3 but 0 Event, 1 Time

pred RedundantSuccessors [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && ! DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run RedundantSuccessors for 2 but 0 Event, 1 Time

pred DisorderedSuccessors [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && ! OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run DisorderedSuccessors for 2 but 0 Event, 1 Time

pred InvalidSuccessors [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ! ValidSuccessorList[t]
   && ReachableSuccessor2[t]
}
run InvalidSuccessors for 4 but 0 Event, 1 Time

pred ExternalSuccessor [t: Time] { 
      OneOrderedRing[t]    
   && ConnectedAppendages[t]
   && AntecedentPredecessors[t] 
   && OrderedAppendages[t]     
   && OrderedMerges[t]        
   && DistinctSuccessors[t]  
   && OrderedSuccessors[t]  
   && ValidSuccessorList[t]
   && ! ReachableSuccessor2[t]
}
run ExternalSuccessor for 3 but 0 Event, 1 Time

pred ValidRingWithOneMember [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 1 && Valid[t] && ! Ideal[t] }
run ValidRingWithOneMember for 1 but 0 Event, 1 Time

pred ValidRingWithTwoMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 2 && Valid[t] && ! Ideal[t] }
run ValidRingWithTwoMembers for 2 but 0 Event, 1 Time

pred ValidRingWithThreeMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 3 && Valid[t] && ! Ideal[t] }
run ValidRingWithThreeMembers for 3 but 0 Event, 1 Time

pred ValidRingWithFourMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 4 && Valid[t] && ! Ideal[t] }
run ValidRingWithFourMembers for 4 but 0 Event, 1 Time

pred ValidRingWithFiveMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 5 && Valid[t] && ! Ideal[t] }
run ValidRingWithFiveMembers for 5 but 0 Event, 1 Time

pred ValidRingWithSixMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | 
      # members = 6 && Valid[t] && ! Ideal[t] }
run ValidRingWithSixMembers for 6 but 0 Event, 1 Time

pred UnStable [t: Time] {  
   Valid[t] && ! Stable[t] && Reconciled[t]  }
run UnStable for 3 but 0 Event, 1 Time

pred UnReconciled [t: Time] {  
   Valid[t] && Stable[t] && ! Reconciled[t]  }
run UnReconciled for 1 but 0 Event, 1 Time

pred IdealRingWithThreeMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | # members = 3 && Ideal[t] }
run IdealRingWithThreeMembers for 3 but 0 Event, 1 Time

pred IdealRingWithFourMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | # members = 4 && Ideal[t] }
run IdealRingWithFourMembers for 4 but 0 Event, 1 Time

pred IdealRingWithFiveMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | # members = 5 && Ideal[t] }
run IdealRingWithFiveMembers for 5 but 0 Event, 1 Time

pred IdealRingWithSixMembers [t: Time] {
   let members = { n: Node | Member[n,t] } | # members = 6 && Ideal[t] }
run IdealRingWithSixMembers for 6 but 0 Event, 1 Time
======================================================================== */
