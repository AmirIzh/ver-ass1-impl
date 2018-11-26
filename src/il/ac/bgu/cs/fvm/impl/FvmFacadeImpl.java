package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.*;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        boolean ans = true;
        Set<A> actions = ts.getActions();
        Set<S> states = ts.getStates();

        if(ts.getInitialStates().size() > 1)
            ans = false;

        for(S state : states){
            for(A action : actions){
                if(post(ts, state, action).size() > 1)
                    ans = false;
            }
        }

        return ans;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        boolean ans = true;
        boolean stop = false;
        Set<S> states = ts.getStates();
        Set<S> postStates;
        Map<Set<P>, Integer> labelCounter;
        Set<P> labels;

        if(ts.getInitialStates().size() > 1)
            ans = false;

        for(S state : states){
            if(stop) break;
            postStates = post(ts, state);
            labelCounter = new HashMap<>();
            for(S postState : postStates){
                if(stop) break;
                labels = ts.getLabel(postState);
                if(labelCounter.get(labels) == null){
                    labelCounter.put(labels, 1);
                }
                else{
                    ans = false;
                    stop = true;
                    break;
                }
            }
        }

        return ans;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        boolean ans = true;
        AlternatingSequence<A, S> actionInHead;
        S state;
        A action;

        while(e.size() > 1){
            state = e.head();
            actionInHead = e.tail();
            action = actionInHead.head();
            e = actionInHead.tail();

            if(post(ts, state, action).size() == 0){
                ans = false;
                break;
            }
            if(!post(ts, state, action).contains(e.head())){
                ans = false;
                break;
            }
        }
        return ans;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        boolean ans = isExecutionFragment(ts, e);

        if(!ts.getInitialStates().contains(e.head()))
            ans = false;

        return ans;
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        boolean ans = isExecutionFragment(ts, e);
        AlternatingSequence<A, S> actionInHead;
        S state;
        A action;

        while(e.size() > 1) {
            state = e.head();
            actionInHead = e.tail();
            action = actionInHead.head();
            e = actionInHead.tail();
        }

        if(!isStateTerminal(ts, e.head()))
            ans = false;

        return ans;
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        boolean ans = true;

        if(post(ts, s).size() > 0)
            ans = false;

        return ans;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if(tra.getFrom().equals(s)){
                ans.add(tra.getTo());
            }
        }
        return ans;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if (c.contains(tra.getFrom())) {
                ans.add(tra.getTo());
            }
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if(tra.getFrom().equals(s) && tra.getAction().equals(a)){
                ans.add(tra.getTo());
            }
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if (c.contains(tra.getFrom()) && tra.getAction().equals(a)) {
                ans.add(tra.getTo());
            }
        }
        return ans;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if(tra.getTo().equals(s)){
                ans.add(tra.getFrom());
            }
        }
        return ans;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if (c.contains(tra.getTo())) {
                ans.add(tra.getFrom());
            }
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if(tra.getTo().equals(s) && tra.getAction().equals(a)){
                ans.add(tra.getFrom());
            }
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if (c.contains(tra.getTo()) && tra.getAction().equals(a)) {
                ans.add(tra.getFrom());
            }
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> ans = new HashSet<>();
        Set<S> initStates = ts.getInitialStates();

        for(S state : initStates){
            recReach(ts, ans, state);
        }

        return ans;
    }

    private <S, A> void recReach(TransitionSystem<S, A, ?> ts, Set<S> ans, S curState){
        ans.add(curState);

        for(S state : post(ts, curState)){
            if(!ans.contains(state))
                recReach(ts, ans, state);
        }
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
//        TransitionSystem<Pair<S1, S2>, A, P> ansTS = createTransitionSystem();
//        Set<Pair<S1, S2>> ansStatesSet = new HashSet<>(), ansInitStatesSet = new HashSet<>();
//        Set<A> ansActionsSet = new HashSet<>();
//        Set<P> ansAtomicPropositionsSet = new HashSet<>(), mergedLabels = new HashSet<>();
//        Set<Transition<S1, A>> traSet1;
//        Set<Transition<S2, A>> traSet2;
//
//        for(S1 state1 : ts1.getStates()){
//            for(S2 state2 : ts2.getStates()){
//                ansStatesSet.add(new Pair(state1, state2));
//            }
//        }
//
//        for(A action : ts1.getActions()){
//            ansActionsSet.add(action);
//        }
//        for(A action : ts2.getActions()){
//            ansActionsSet.add(action);
//        }
//
//        for(S1 initState1 : ts1.getInitialStates()){
//            for(S2 initState2 : ts2.getInitialStates()){
//                ansInitStatesSet.add(new Pair(initState1, initState2));
//            }
//        }
//
//        for(P ap : ts1.getAtomicPropositions()){
//            ansAtomicPropositionsSet.add(ap);
//        }
//        for(P ap : ts2.getAtomicPropositions()){
//            ansAtomicPropositionsSet.add(ap);
//        }
//
//        for(Pair<S1, S2> statePair : ansStatesSet){
//            mergedLabels.addAll(ts1.getLabel(statePair.first));
//            mergedLabels.addAll(ts2.getLabel(statePair.second));
//            for(P label : mergedLabels){
//                ansTS.addToLabel(statePair, label);
//            }
//        }
//
//        traSet1 = ts1.getTransitions();
//        traSet2 = ts2.getTransitions();
//        for(Transition<S1, A> tra : traSet1){
//            ts1.get
//        }
//
//        return ansTS;
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem = createTransitionSystem();

        for(L location: pg.getLocations()){
            transitionSystem.addAtomicProposition(location.toString());
        }

        // get all initial assignments
        Set<Map<String, Object>> initialAssignments = new HashSet<>();
        for (List<String> initialization : pg.getInitalizations()) {
            Map<String, Object> assignment = new HashMap<>();
            for (String varInit : initialization) {
                assignment = ActionDef.effect(actionDefs, assignment, varInit); //The varInit here is the "action"
            }
            initialAssignments.add(assignment);
        }

        // Set initial States to the transitionSystem
        for(L initLoc : pg.getInitialLocations()){
            for(Map<String, Object> initAss: initialAssignments) {
                Pair<L, Map<String, Object>> state = new Pair<>(initLoc, initAss);
                transitionSystem.addState(state);
                transitionSystem.setInitial(state, true);
            }
        }

        Set<Pair<L, Map<String, Object>>> currStates = new HashSet<>(transitionSystem.getInitialStates());
        while(!currStates.isEmpty()){
            Pair<L, Map<String, Object>> currState = currStates.iterator().next();
            L initLoc = currState.getFirst();
            for(PGTransition<L,A> transition: pg.getTransitions()){
                if(initLoc.equals(transition.getFrom())){
                    Map<String,Object> initEval = currState.getSecond();
                    String condition = transition.getCondition();
                    if(ConditionDef.evaluate(conditionDefs,initEval,condition)){ // if the condition is valid for the current eval
//                        transitionSystem.addAtomicProposition(condition);
//                        transitionSystem.addToLabel(currState, condition);
                        A action = transition.getAction();
                        Map<String,Object> evalAfterEffect = ActionDef.effect(actionDefs,initEval,action);
                        Pair<L, Map<String, Object>> newState = new Pair<>(transition.getTo(),evalAfterEffect);
                        if(!transitionSystem.getStates().contains(newState)) {
                            currStates.add(newState);
                        }
                        transitionSystem.addState(newState);
                        Transition<Pair<L, Map<String, Object>>, A> newTransition = new Transition<>(currState,action, newState);
                        transitionSystem.addAction(action);
                        transitionSystem.addTransition(newTransition);
                    }
                }
            }
            currStates.remove(currState);
        }

        for(Pair<L, Map<String, Object>> state: transitionSystem.getStates()){
            transitionSystem.addToLabel(state, state.getFirst().toString());
            for(String var : state.getSecond().keySet()){
                String varAssignmentExp = var + " = " + state.getSecond().get(var);
                transitionSystem.addAtomicProposition(varAssignmentExp);
                transitionSystem.addToLabel(state,varAssignmentExp);
            }
        }
        return transitionSystem;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }
   
}
