package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import org.antlr.v4.runtime.tree.ParseTree;

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
            if(!ts.getStates().contains(state)) throw new StateNotFoundException(state);
            actionInHead = e.tail();
            action = actionInHead.head();
            if(!ts.getActions().contains(action)) throw new ActionNotFoundException(action);
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

        if(!ts.getStates().contains(s)) throw new StateNotFoundException(s);

        for(Transition<S, ?> tra : traSet){
            if(tra.getFrom().equals(s))
                ans.add(tra.getTo());

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

        if(!ts.getStates().contains(s)) throw new StateNotFoundException(s);

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
            if (c.contains(tra.getTo()))
                ans.add(tra.getFrom());
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        if(!ts.getStates().contains(s)) throw new StateNotFoundException(s);

        for(Transition<S, ?> tra : traSet){
            if(tra.getTo().equals(s) && tra.getAction().equals(a))
                ans.add(tra.getFrom());
        }
        return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ans = new HashSet<>();
        Set<? extends Transition<S, ?>> traSet = ts.getTransitions();

        for(Transition<S, ?> tra : traSet){
            if (c.contains(tra.getTo()) && tra.getAction().equals(a))
                ans.add(tra.getFrom());

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
                postSPerAction = postPerActionMap.get(keyPair);
                for(S to : postSPerAction){
                    if (first) ansTran = new Transition<>(statePair, action, new Pair<>((S1) to, statePair.second));
                    else ansTran = new Transition<>(statePair, action, new Pair<>(statePair.first, (S2) to));
                    ansTransitions.add(ansTran);
                }
            }
        }

        return ansTransitions;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> ansTS = makeInterleaveNoTransitions(ts1, ts2);
        Set<Pair<S1, S2>> ansStatesSet = makeInterleaveStatesSet(ts1, ts2), reachableStates, allStates = new HashSet<>();
        Set<Transition<Pair<S1, S2>, A>> ansTransitions = new HashSet<>(), allTrans = new HashSet<>();

        // ------------------ fill the ansTransitions and insert to ansTS -------------------
        ansTransitions.addAll(makeInterleaveTransitions(ts1, ansStatesSet, ts1.getActions(), true));
        ansTransitions.addAll(makeInterleaveTransitions(ts2, ansStatesSet, ts2.getActions(), false));
        makeInterleaveTransitionsHandShake(ansTransitions, ts1, ts2, handShakingActions);
        for(Transition<Pair<S1, S2>, A> tra : ansTransitions){
            ansTS.addTransition(tra);
        }

        // ------------------ removing non-reachable states and transitions -------------------
        reachableStates = reach(ansTS);
        allTrans.addAll(ansTransitions);
        for(Transition<Pair<S1, S2>, A> tra : allTrans){
            if(!reachableStates.contains(tra.getTo()) || !reachableStates.contains(tra.getFrom())){
                ansTS.removeTransition(tra);
            }
        }
        allStates.addAll(ansTS.getStates());
        for(Pair<S1, S2> state : allStates){
            if(!reachableStates.contains(state)){
                ansTS.removeState(state);
            }
        }


        return ansTS;
    }

    private <S, S1, S2, A, P> void makeInterleaveTransitionsHandShake(Set<Transition<Pair<S1, S2>, A>> ansTransitions, TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions){
        Pair<S1, S2> from, to;
        Set<Transition<Pair<S1, S2>, A>> transToInsert = new HashSet<>();
        Set<Transition<Pair<S1, S2>, A>> transToRemove = new HashSet<>();

        for(Transition<Pair<S1, S2>, A> tra : ansTransitions){
            if(handShakingActions.contains(tra.getAction())){
                from = tra.getFrom();
                to = tra.getTo();
                if(from.first.equals(to.first)) removeAndAddHSTrans(transToInsert, transToRemove, ts1, tra, from.first, true);
                else if(from.second.equals(to.second)) removeAndAddHSTrans(transToInsert, transToRemove, ts2, tra, from.second, false);
            }
        }
        ansTransitions.removeAll(transToRemove);
        ansTransitions.addAll(transToInsert);


    }

    private <S, S1, S2, A, P> void removeAndAddHSTrans(Set<Transition<Pair<S1, S2>, A>> transToInsert, Set<Transition<Pair<S1, S2>, A>> transToRemove,  TransitionSystem<S, A, P> ts, Transition<Pair<S1, S2>, A> tra, S sameState, boolean first){
        Set<S> postWithAction = post(ts, sameState, tra.getAction());
        Transition<Pair<S1, S2>, A> toInsert;

        transToRemove.add(tra);
        if(postWithAction.size() > 0){
            for(S postState : postWithAction){
                if(first) toInsert = new Transition<>(tra.getFrom(), tra.getAction(), new Pair<>((S1)postState, tra.getTo().second));
                else toInsert = new Transition<>(tra.getFrom(), tra.getAction(), new Pair<>(tra.getTo().first, (S2)postState));
                transToInsert.add(toInsert);
            }
        }
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleavedProgramGraph = new ProgramGraphImpl<>();

        Set<Pair<L1,L2>> locationPairs = locationsCartesianProduct(pg1.getLocations(), pg2.getLocations());
        for(Pair<L1,L2> pair: locationPairs){
            interleavedProgramGraph.addLocation(pair);
        }

        Set<Pair<L1,L2>> initialLocationPairs = locationsCartesianProduct(pg1.getInitialLocations(), pg2.getInitialLocations());
        for(Pair<L1,L2> pair: initialLocationPairs){
            interleavedProgramGraph.setInitial(pair, true);
        }

        for(List<String> initialization: interleaveInitializations(pg1.getInitalizations(),pg2.getInitalizations())){
            interleavedProgramGraph.addInitalization(initialization);
        }

        for(PGTransition<L1,A> transition: pg1.getTransitions()){
            for(Pair<L1,L2> location: interleavedProgramGraph.getLocations()){
                if(location.getFirst().equals(transition.getFrom())){
                    PGTransition<Pair<L1,L2>,A> newTransition = new PGTransition<>(location, transition.getCondition(), transition.getAction(), new Pair<>(transition.getTo(),location.getSecond()));
                    interleavedProgramGraph.addTransition(newTransition);
                }
            }
        }

        for(PGTransition<L2,A> transition: pg2.getTransitions()){
            for(Pair<L1,L2> location: interleavedProgramGraph.getLocations()){
                if(location.getSecond().equals(transition.getFrom())){
                    PGTransition<Pair<L1,L2>,A> newTransition = new PGTransition<>(location, transition.getCondition(), transition.getAction(), new Pair<>(location.getFirst(),transition.getTo()));
                    interleavedProgramGraph.addTransition(newTransition);
                }
            }
        }
        return interleavedProgramGraph;

    }

    private Set<List<String>> interleaveInitializations(Set<List<String>> initializations1, Set<List<String>> initializations2){
        Set<List<String>> interleavedInitializations = new HashSet<>();
        for(List<String> initialization1: initializations1){
            for(List<String> initialization2: initializations2){
                List<String> initializationsList = new LinkedList<>();
                initializationsList.addAll(initialization1);
                initializationsList.addAll(initialization2);
                interleavedInitializations.add(	new LinkedList<>(initializationsList));
            }
        }
        return interleavedInitializations;
    }

    private <L1, L2> Set<Pair<L1,L2>> locationsCartesianProduct(Set<L1> locations1, Set<L2> locations2) {
        Set<Pair<L1, L2>> locations = new HashSet<>();
        for (L1 l1: locations1) {
            for(L2 l2: locations2){
                locations.add(new Pair<>(l1,l2));
            }
        }
        return locations;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ansTS = new TransitionSystemImpl<>();
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> states = new HashSet<>();
        Map<String, Boolean> regMap;
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> statesCopy;
        Set<String> inputs = c.getInputPortNames(), registers = c.getRegisterNames(), outputs = c.getOutputPortNames();
        Pair<Map<String, Boolean>, Map<String, Boolean>> newState;
        Set<String> labels;
        Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> newTran;
        Set<Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitions = new HashSet<>();
        int actionsSize, changeNumber, x = 1, mapCounter, oldStateCopySize = 0, finalStateSize;


        // ------------------ make the actions, and insert to ansTS -------------------
        actionsSize = (int)Math.pow(2, inputs.size());
        Map<String, Boolean>[] actionsArr = new HashMap[actionsSize];
        Object[] inputsArr = inputs.toArray();
        for(int i = 0; i < actionsSize; i++){
            actionsArr[i] = new HashMap<>();
        }
        changeNumber = actionsSize;
        for(int i = 0; i < inputs.size(); i++, x = x * 2){
            mapCounter = 0;
            changeNumber = changeNumber / 2;
            for(int j = 0; j < x; j++){
                for(int t = changeNumber; t > 0; t = t / 2){
                    actionsArr[mapCounter].put((String)inputsArr[i], true);// לשים טרו
                    mapCounter++;
                }
                for(int t = changeNumber; t > 0; t = t / 2){
                    actionsArr[mapCounter].put((String)inputsArr[i], false);// לשים פולס
                    mapCounter++;
                }
            }
        }
        ansTS.addAllActions(actionsArr);

        // ------------------ make the initial states, and insert to ansTS -------------------
        while(states.size() < Math.pow(2, inputs.size())){
            for(Map<String, Boolean> action : ansTS.getActions()){
                regMap = new HashMap<>();
                for(String reg : registers){
                    regMap.put(reg, false);
                }
                states.add(new Pair<>(action, regMap));
            }
        }
        ansTS.addAllStates(states);
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> state : states){
            ansTS.setInitial(state, true);
        }

        // ------------------ make the other states + transitions, and insert to ansTS -------------------
        statesCopy = new HashSet<>();
        statesCopy.addAll(states);
        finalStateSize =  Integer.MAX_VALUE / ansTS.getActions().size();
        while(transitions.size() < (finalStateSize * ansTS.getActions().size())){
            oldStateCopySize = statesCopy.size();
            for(Pair<Map<String, Boolean>, Map<String, Boolean>> state : statesCopy){
                for(Map<String, Boolean> action : ansTS.getActions()){
                    newState = new Pair<>(action, c.updateRegisters(state.first, state.second));
                    states.add(newState);
                    newTran = new Transition<>(state, action, newState);
                    transitions.add(newTran);
                }
            }
            statesCopy.addAll(states);
            if(oldStateCopySize == statesCopy.size()){
                finalStateSize = oldStateCopySize;
            }
        }
        ansTS.addAllStates(states);
        for(Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> tra : transitions)
            ansTS.addTransition(tra);


        // ------------------ make the atomic props, and insert to ansTS -------------------
        ansTS.addAllAtomicPropositions(inputs.toArray());
        ansTS.addAllAtomicPropositions(registers.toArray());
        ansTS.addAllAtomicPropositions(outputs.toArray());

        // ------------------ label the states in ansTS -------------------
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> state : states){
            labels = new HashSet<>();
            for(String input : inputs){
                if(state.first.get(input))
                    labels.add(input);
            }
            for(String reg : registers){
                if(state.second.get(reg))
                    labels.add(reg);
            }
            for(String output : outputs){
                if(c.computeOutputs(state.first, state.second).get(output))
                    labels.add(output);
            }
            for(String label : labels)
                ansTS.addToLabel(state, label);
        }

        return ansTS;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem = createTransitionSystem();

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
            transitionSystem.addAtomicProposition(currState.getFirst().toString());
            L initLoc = currState.getFirst();
            for(PGTransition<L,A> transition: pg.getTransitions()){
                if(initLoc.equals(transition.getFrom())){
                    Map<String,Object> initEval = currState.getSecond();
                    String condition = transition.getCondition();
                    if(ConditionDef.evaluate(conditionDefs,initEval,condition)){ // if the condition is valid for the current eval
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
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    private void PGFromNP(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int childCount = myRoot.getChildCount();
        String child;

        if(myRoot instanceof NanoPromelaParser.IfstmtContext)
            processIf(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(myRoot instanceof NanoPromelaParser.DostmtContext)
            processDo(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(!(myRoot instanceof NanoPromelaParser.StmtContext))
            processOtherCase(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(childCount > 1){
            child = myRoot.getChild(1).getText();
            if(child.equals(";"))
                processStmt(ansPG, myRoot, fromNode, toNode, cond, post_np);
        }
        else
            PGFromNP(ansPG, myRoot.getChild(0), fromNode, toNode, cond, post_np);
    }

    private void processIf(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int rootChildNum = myRoot.getChildCount() - 1;
        String ansCond, bracketsCond, ifCond;
        ParseTree child;

        for(int i = 1; i < rootChildNum; i++){
            child = myRoot.getChild(i).getChild(3);
            bracketsCond = "(" + cond + ")";
            ifCond = "(" + myRoot.getChild(i).getChild(1).getText() + ")";

            if(bracketsCond.equals("()"))
                ansCond = ifCond;
            else if(ifCond.equals("()"))
                ansCond = bracketsCond;
            else
                ansCond = bracketsCond + " && " + ifCond;

            PGFromNP(ansPG, child, fromNode, toNode, ansCond, post_np);
        }
    }

    private <L, A> void processDo(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int rootChildNum = myRoot.getChildCount() - 1;
        String neg = "", ansCond, fromTransAns, rootTXT = myRoot.getText(), from_trans3 = toNode + post_np, consitionTransAns, notBracketsNeg;

        for(int i = 1; i < rootChildNum; i++){
            DoHelper(ansPG, myRoot, fromNode, toNode, cond, post_np, i);
            ansCond = myRoot.getChild(i).getChild(1).getText();
            neg = "(" + ansCond + ")";
        }

        if(rootTXT.equals("") || rootTXT.equals("()")) fromTransAns = from_trans3;
        else if(from_trans3.equals("") || from_trans3.equals("()")) fromTransAns = rootTXT;
        else fromTransAns = rootTXT + ";" + from_trans3;

        notBracketsNeg = "(!(" + neg + "))";
        if(cond.equals("") || cond.equals("()")) consitionTransAns = notBracketsNeg;
        else if(notBracketsNeg.equals("()")) consitionTransAns = cond;
        else consitionTransAns = cond + " && " + notBracketsNeg;

        PGTransition<L, A> trans_pg = new PGTransition<>((L)fromTransAns, notBracketsNeg, (A) "", (L)(toNode + post_np));
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg);

        PGTransition<L, A> trans_pg1 = new PGTransition<>((L)fromNode, consitionTransAns, (A) "", (L)(toNode + post_np));
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg1.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg1.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg1);
    }

    private void DoHelper(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np, int i){
        String ansCond = myRoot.getChild(i).getChild(1).getText();
        ParseTree child = myRoot.getChild(i).getChild(3);
        String rootTXT = myRoot.getText(), ansPost, bracketsCond, cond3, ansCondUpdate, ansFrom, ansFromFinal;

        if(rootTXT.equals("") || rootTXT.equals("()")) ansPost = post_np;
        else if(post_np.equals("") || post_np.equals("()")) ansPost = rootTXT;
        else ansPost = rootTXT + ";" + post_np;

        bracketsCond = "(" + cond + ")";
        cond3 = "(" + ansCond + ")";
        if(bracketsCond.equals("()")) ansCondUpdate = cond3;
        else if(cond3.equals("()")) ansCondUpdate = bracketsCond;
        else ansCondUpdate = bracketsCond + " && " + cond3;

        if(rootTXT.equals("") || rootTXT.equals("()")) ansFrom = toNode;
        else if(toNode.equals("") || toNode.equals("()")) ansFrom = rootTXT;
        else ansFrom = rootTXT + ";" + toNode;

        if(ansFrom.equals("") || ansFrom.equals("()")) ansFromFinal = post_np;
        else if(post_np.equals("") || post_np.equals("()")) ansFromFinal = ansFrom;
        else ansFromFinal = ansFrom + ";" + post_np;

        PGFromNP(ansPG, child, fromNode, toNode, ansCondUpdate, ansPost);
        PGFromNP(ansPG, child, ansFromFinal, toNode, cond3, ansPost);
    }

    private <L, A> void processOtherCase(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np) {
        String to_ans;

        if(toNode.equals("") || toNode.equals("()")) to_ans = post_np;
        else if(post_np.equals("") || post_np.equals("()")) to_ans = toNode;
        else to_ans = toNode + ";" + post_np;

        PGTransition<L, A> trans_pg = new PGTransition<>((L)fromNode, cond, (A)myRoot.getText(), (L)to_ans);
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg);
    }

    private void processStmt(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        ParseTree child0 = myRoot.getChild(0), child2 = myRoot.getChild(2);
        String child2TXT = child2.getText(), post_ans;

        if(child2TXT.equals("") || child2TXT.equals("()")) post_ans = post_np;
        else if(post_np.equals("") || post_np.equals("()")) post_ans = child2TXT;
        else post_ans = child2TXT + ";" + post_np;

        PGFromNP(ansPG, child0, fromNode, toNode, cond, post_ans);
        PGFromNP(ansPG, child2, post_ans, toNode, "", post_np);
        }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
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
