package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ProgramGraphImpl<L,A> implements ProgramGraph<L,A> {

    private String name;
    private Set<L> locations;
    private Set<L> initialLocations;
    private Set<List<String>> initializations;
    private Set<PGTransition<L, A>> transitions;


    public ProgramGraphImpl(){
        this.locations = new HashSet<>();
        this.initialLocations = new HashSet<>();
        this.initializations = new HashSet<>();
        this.transitions = new HashSet<>();
    }


    @Override
    public void addInitalization(List<String> init) {
        this.initializations.add(init);
    }

    @Override
    public void setInitial(L location, boolean isInitial) {
        if(!this.locations.contains(location)){
            throw new IllegalArgumentException("Location ("+location + ") is not a location in this Program Graph.");
        }
        if(isInitial){
            initialLocations.add(location);
        }
        else this.initialLocations.remove(location);
    }

    @Override
    public void addLocation(L l) {
        this.locations.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        this.transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return this.initializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return this.initialLocations;
    }

    @Override
    public Set<L> getLocations() {
        return this.locations;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeLocation(L l) {
        this.locations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        this.transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
