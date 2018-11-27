package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;

public class TransitionSystemImpl<STATE,ACTION,ATOMIC_PROPOSITION>  implements TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION> {

    private String name;
    private Set<STATE> states;
    private Set<STATE> initials;
    private Set<ACTION> actions;
    private Set<Transition<STATE,ACTION>> transitions;
    private Set<ATOMIC_PROPOSITION> atomicPropositions;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labelingFunction;

    public TransitionSystemImpl(){
        this.name = "";
        this.states = new HashSet<>();
        this.initials = new HashSet<>();
        this.actions = new HashSet<>();
        this.transitions = new HashSet<>();
        this.atomicPropositions = new HashSet<>();
        this.labelingFunction = new HashMap<>();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION anAction) {
        actions.add(anAction);
    }

    @Override
    public  void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
        if(!this.states.contains(aState)){
            throw new StateNotFoundException(aState);
        }
        if(isInitial){
            initials.add(aState);
        }
        else if(this.initials.contains(aState)){
            this.initials.remove(aState);
        }
    }

    @Override
    public void addState(STATE o) {
        this.states.add(o);
        this.labelingFunction.put(o, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<STATE,ACTION> t) throws FVMException {
        if(!this.states.contains(t.getFrom()) || !this.states.contains(t.getTo()) || !this.actions.contains(t.getAction())){
            throw new InvalidTransitionException(t);
        }
        else{
            this.transitions.add(t);
        }
    }

    @Override
    public Set<ACTION> getActions() {
        return this.actions;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        this.atomicPropositions.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return this.atomicPropositions;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if(!this.states.contains(s)){
            throw new StateNotFoundException(s);
        }
        else if(!this.atomicPropositions.contains(l)){
            throw new InvalidLablingPairException(s, l);
        }
        else{
            this.labelingFunction.get(s).add(l);
        }
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s){
        if(!this.states.contains(s)){
            throw new StateNotFoundException(s);
        }
        return this.labelingFunction.get(s);
    }

    @Override
    public Set<STATE> getInitialStates() {
        return this.initials;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return this.labelingFunction;
    }

    @Override
    public Set<STATE> getStates() {
        return this.states;
    }

    @Override
    public Set<Transition<STATE,ACTION>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeAction(ACTION o) throws FVMException {
        for(Transition transition : this.transitions){
            if(transition.getAction().equals(o)){
                throw new DeletionOfAttachedActionException(o, TransitionSystemPart.TRANSITIONS);
            }
        }
        this.actions.remove(o);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        for(Set<ATOMIC_PROPOSITION> apSet: this.labelingFunction.values()){
            if(apSet.contains(p)){
                throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.LABELING_FUNCTION);
            }
        }
        this.atomicPropositions.remove(p);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        this.labelingFunction.get(s).remove(l);
    }

    @Override
    public void removeState(STATE o) throws FVMException {
        for(Transition transition : this.transitions){
            if(transition.getFrom().equals(o) || transition.getTo().equals(o)){
                throw new DeletionOfAttachedStateException(o, TransitionSystemPart.TRANSITIONS);
            }
        }
        if(this.initials.contains(o)){
            throw new DeletionOfAttachedStateException(o, TransitionSystemPart.INITIAL_STATES);
        }
        else if(this.labelingFunction.get(o).isEmpty()){
            this.labelingFunction.remove(o);
        }
        else{
            throw new DeletionOfAttachedStateException(o, TransitionSystemPart.LABELING_FUNCTION);
        }
        this.states.remove(o);
    }

    @Override
    public void removeTransition(Transition t) {
        this.transitions.remove(t);
    }
}
