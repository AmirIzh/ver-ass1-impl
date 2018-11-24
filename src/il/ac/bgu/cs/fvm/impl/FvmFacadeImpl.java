package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createTransitionSystem
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

        while(e.size() > 1) {
            actionInHead = e.tail();
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
        TransitionSystem<Pair<S1, S2>, A, P> ansTS = makeInterleaveNoTransitions(ts1, ts2);
        Set<Pair<S1, S2>> ansStatesSet = makeInterleaveStatesSet(ts1, ts2);
        Set<Transition<Pair<S1, S2>, A>> ansTransitions = new HashSet<>();

        // ------------------ fill the ansTransitions and insert to ansTS -------------------
        ansTransitions.addAll(makeInterleaveTransitions(ts1, ansStatesSet, ts1.getActions(), true));
        ansTransitions.addAll(makeInterleaveTransitions(ts2, ansStatesSet, ts2.getActions(), false));
        for(Transition<Pair<S1, S2>, A> tra : ansTransitions){
            ansTS.addTransition(tra);
        }

        return ansTS;
    }

    private <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> makeInterleaveNoTransitions(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2){
        TransitionSystem<Pair<S1, S2>, A, P> ansTS = createTransitionSystem();
        Set<Pair<S1, S2>> ansStatesSet, ansInitStatesSet;

        // ------------------ make ansStatesSet and insert to ansTS -------------------
        ansStatesSet = makeInterleaveStatesSet(ts1, ts2);
        ansTS.addAllStates(ansStatesSet);

        // ------------------ make ansActionsSet and insert to ansTS -------------------
        ansTS.addAllActions(makeInterleaveActionsSet(ts1, ts2));

        // ------------------ fill ansInitStatesSet and insert to ansTS -------------------
        ansInitStatesSet = makeInterleaveInitStatesSet(ts1, ts2);
        for(Pair<S1, S2> initState : ansInitStatesSet){
            ansTS.setInitial(initState, true);
        }

        // ------------------ fill ansAtomicPropositionsSet and insert to ansTS -------------------
        ansTS.addAllAtomicPropositions(makeInterleaveAtomicPropSet(ts1, ts2));

        // ------------------ make the labeling function and insert to ansTS -------------------
        makeInterleaveLabelFunc(ansTS, ts1, ts2, ansStatesSet);

        return ansTS;
    }

    private <S1, S2, A, P> Set<Pair<S1, S2>> makeInterleaveStatesSet(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2){
        Set<Pair<S1, S2>> ansStatesSet = new HashSet<>();

        for(S1 state1 : ts1.getStates()){
            for(S2 state2 : ts2.getStates()){
                ansStatesSet.add(new Pair<>(state1, state2));
            }
        }

        return ansStatesSet;
    }

    private <S1, S2, A, P> Set<A> makeInterleaveActionsSet(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2){
        Set<A> ansActionsSet = new HashSet<>();

        ansActionsSet.addAll(ts1.getActions());
        ansActionsSet.addAll(ts2.getActions());

        return ansActionsSet;
    }

    private <S1, S2, A, P> Set<Pair<S1, S2>> makeInterleaveInitStatesSet(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2){
        Set<Pair<S1, S2>> ansInitStatesSet = new HashSet<>();

        for(S1 initState1 : ts1.getInitialStates()){
            for(S2 initState2 : ts2.getInitialStates()){
                ansInitStatesSet.add(new Pair<>(initState1, initState2));
            }
        }

        return ansInitStatesSet;
    }

    private <S1, S2, A, P> Set<P> makeInterleaveAtomicPropSet(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2){
        Set<P> ansAtomicPropositionsSet = new HashSet<>();

        ansAtomicPropositionsSet.addAll(ts1.getAtomicPropositions());
        ansAtomicPropositionsSet.addAll(ts2.getAtomicPropositions());

        return ansAtomicPropositionsSet;
    }

    private <S1, S2, A, P> void makeInterleaveLabelFunc(TransitionSystem<Pair<S1, S2>, A, P> ansTS, TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<Pair<S1, S2>> ansStatesSet){
        Set<P> mergedLabels;

        for(Pair<S1, S2> statePair : ansStatesSet){
            mergedLabels = new HashSet<>();
            mergedLabels.addAll(ts1.getLabel(statePair.first));
            mergedLabels.addAll(ts2.getLabel(statePair.second));
            for(P label : mergedLabels){
                ansTS.addToLabel(statePair, label);
            }
        }
    }

    private <S, S1, S2,  A, P> Set<Transition<Pair<S1, S2>, A>> makeInterleaveTransitions(TransitionSystem<S, A, P> ts, Set<Pair<S1, S2>> ansStatesSet, Set<A> ansActions, boolean first){
        Set<Transition<Pair<S1, S2>, A>> ansTransitions = new HashSet<>();
        Map<Pair<S, A>, Set<S>> postPerActionMap = new HashMap<>();
        Transition<Pair<S1, S2>, A> ansTran;
        Set<S> postSPerAction;
        Pair<S, A> keyPair;

        for(Pair<S1, S2> statePair : ansStatesSet){
            for(A action : ansActions){
                if(first) keyPair = new Pair<>((S)statePair.first, action);
                else keyPair = new Pair<>((S)statePair.second, action);
                postSPerAction = postPerActionMap.get(keyPair);
                if(postSPerAction == null){
                    if(first) postPerActionMap.put(keyPair, post(ts, (S)statePair.first, action));
                    else postPerActionMap.put(keyPair, post(ts, (S)statePair.second, action));
                }
                else{
                    for(S to : postSPerAction){
                        if(first) ansTran = new Transition<>(statePair, action, new Pair<>((S1)to, statePair.second));
                        else ansTran = new Transition<>(statePair, action, new Pair<>(statePair.first, (S2)to));
                        ansTransitions.add(ansTran);
                    }
                }
            }
        }

        return ansTransitions;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> ansTS = makeInterleaveNoTransitions(ts1, ts2);
        Set<Pair<S1, S2>> ansStatesSet = makeInterleaveStatesSet(ts1, ts2);
        Set<Transition<Pair<S1, S2>, A>> ansTransitions = new HashSet<>();

        // ------------------ fill the ansTransitions and insert to ansTS -------------------
        ansTransitions.addAll(makeInterleaveTransitions(ts1, ansStatesSet, ts1.getActions(), true));
        ansTransitions.addAll(makeInterleaveTransitions(ts2, ansStatesSet, ts2.getActions(), false));
        makeInterleaveTransitionsHandShake(ansTransitions, ts1, ts2, handShakingActions);
        for(Transition<Pair<S1, S2>, A> tra : ansTransitions){
            ansTS.addTransition(tra);
        }

        return ansTS;
    }

    private <S, S1, S2, A, P> void makeInterleaveTransitionsHandShake(Set<Transition<Pair<S1, S2>, A>> ansTransitions, TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions){
        Pair<S1, S2> from, to;

        for(Transition<Pair<S1, S2>, A> tra : ansTransitions){
            if(handShakingActions.contains(tra.getAction())){
                from = tra.getFrom();
                to = tra.getTo();
                if(from.first.equals(to.first)) removeAndAddHSTrans(ansTransitions, ts1, tra, from.first, true);
                else if(from.second.equals(to.second)) removeAndAddHSTrans(ansTransitions, ts2, tra, from.second, false);
            }
        }
    }

    private <S, S1, S2, A, P> void removeAndAddHSTrans(Set<Transition<Pair<S1, S2>, A>> ansTransitions, TransitionSystem<S, A, P> ts, Transition<Pair<S1, S2>, A> tra, S sameState, boolean first){
        Set<S> postWithAction = post(ts, sameState, tra.getAction());
        Transition<Pair<S1, S2>, A> toInsert;

        if(postWithAction.size() > 0){
            ansTransitions.remove(tra);
            for(S postState : postWithAction){
                if(first) toInsert = new Transition<>(tra.getFrom(), tra.getAction(), new Pair<>((S1)postState, tra.getTo().second));
                else toInsert = new Transition<>(tra.getFrom(), tra.getAction(), new Pair<>(tra.getTo().first, (S2)postState));
                ansTransitions.add(toInsert);
            }
        }
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
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
