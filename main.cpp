#ifndef __PROGTEST__

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <variant>
#include <vector>

using State = unsigned int;
using Symbol = uint8_t;
#endif

using namespace std;
using Config = pair<State, Symbol>;

#ifndef __PROGTEST__

struct NFA {
    set<State> m_States;
    set<Symbol> m_Alphabet;
    map<Config, set<State>> m_Transitions;
    State m_InitialState;
    set<State> m_FinalStates;
};

struct DFA {
    set<State> m_States;
    set<Symbol> m_Alphabet;
    map<Config, State> m_Transitions;
    State m_InitialState;
    set<State> m_FinalStates;
};

// --- Printing ---------------------------------------------------------------
template<typename T1, typename T2>
ostream& operator<<(ostream& out, const pair<T1, T2>& data);
template<typename... T>
ostream& operator<<(ostream& out, const tuple<T...>& data);
template<typename T>
ostream& operator<<(ostream& out, const vector<T>& data);
template<typename T>
ostream& operator<<(ostream& out, const set<T>& data);
template<typename T1, typename T2>
ostream& operator<<(ostream& out, const map<T1, T2>& data);

template<typename T1, typename T2>
ostream& operator<<(ostream& out, const pair<T1, T2>& data) {
    return out << "<" << data.first << " " << data.second << ">";
}

template<size_t I = 0, typename... Tp>
void tuplePrintImpl(ostream& out, const tuple<Tp...>& t) {
    if constexpr (I != 0) out << " ";
    out << get<I>(t);

    if constexpr(I+1 != sizeof...(Tp))
        tuplePrintImpl<I+1>(out, t);
}

template<typename... T>
ostream& operator<<(ostream& out, const tuple<T...>& data) {
    out << "<";
    tuplePrintImpl(out, data);
    return out << ">";
}

template<typename T>
ostream& operator<<(ostream& out, const vector<T>& data) {
    out << "(";
    bool isFirst = true;
    for (const auto& item: data) {
        if (isFirst) isFirst = false;
        else out << " ";
        out << item;
    }
    return out << ")";
}

template<typename T>
ostream& operator<<(ostream& out, const set<T>& data) {
    out << "[";
    for (const auto& item: data)
        out << (item == *data.begin() ? "" : " ") << item;
    return out << "]";
}

template<typename T1, typename T2>
ostream& operator<<(ostream& out, const map<T1, T2>& data) {
    out << "{";
    for (const auto& item: data)
        out << (item == *data.begin() ? "" : " ")
            << "(" << item.first << " " << item.second << ")";
    return out << "}";
}

#endif

/** Checks if two sets intersect, return true if yes */
template<typename S>
bool checkIntersect(const set<S>& s1, const set<S>& s2) {
    auto first1 = s1.begin();
    auto first2 = s2.begin();
    const auto last1 = s1.end();
    const auto last2 = s2.end();

    while (first1 != last1 && first2 != last2) {
        if (*first1 < *first2) {
            ++first1;
        } else  {
            if (!(*first2 < *first1))
                return true;
            ++first2;
        }
    }
    return false;
}

template<typename Automat>
set<Symbol> commonAlphabet(const Automat& aut1, const Automat& aut2) {
    set<Symbol> alphabet;
    merge(
            aut1.m_Alphabet.begin(), aut1.m_Alphabet.end(), 
            aut2.m_Alphabet.begin(), aut2.m_Alphabet.end(), 
            inserter(alphabet, alphabet.begin())
         ); 
    return alphabet;
}

/** Creates a mapping for FromState -> State */
template<typename FromConfig, typename FromState>
map<FromState, State> nameStates(
        const FromState& initial,
        const map<FromConfig, FromState>& transitions
        ) {
    map<FromState, State> nameMaping;

    // starts at 0
    State nextStateName = 0;

    set<FromState> visited = {initial};
    queue<FromState> queue;
    queue.push(initial);

    // BFS
    while (!queue.empty()) {
        const State name = nextStateName++;
        const FromState& state = queue.front();

        // add to the final result
        nameMaping.emplace(make_pair(state, name));

        // adds other to queue in lexicographical order
        auto itr = transitions.lower_bound({state, 0});
        for (; itr != transitions.end() && get<0>(itr -> first) == state; ++itr) {
            const FromState& targets = itr -> second;
            if (visited.find(targets) == visited.end()) {
                visited.emplace(targets);
                queue.emplace(targets);
            }
        }

        queue.pop();
    }
    return nameMaping;
}
/**
 * Renames nodes according to the previously generated mapping 
 * and creates the finite notes set. Puts it all into the final DFA */
DFA commonApplyNaming(
        const DFA& dfa,
        const map<Config, State>& transitions,
        const map<State, State>& nameMaping
        ) {

    // states are just integers in [0, n>
    set<State> newStates = {0}; // the initial state must be always presented
    for (size_t i = 0; i < nameMaping.size(); ++i)
        newStates.emplace(i);

    map<Config, State> newTransitions;

    for (const auto& transition : transitions) {
        const auto& [setConfig, dest] = transition;
        const auto [state, symbol] = setConfig;

        if (nameMaping.count(state) == 0)
            continue;

        // extract names
        const State name = nameMaping.at(state);
        const Config key = Config{name, symbol};
        const State value = nameMaping.at(dest);

        // add to the final result
        newTransitions.emplace(make_pair(key, value));
    }

    set<State> newFinite;
    for (const State fin : dfa.m_FinalStates)
        newFinite.emplace(nameMaping.at(fin));

    const DFA output = {
        newStates,
        dfa.m_Alphabet,
        newTransitions,
        0,
        newFinite
    };

    return output;
}

DFA commonNaming(const DFA& dfa) {
    const map<State, State> nameMaping = nameStates(dfa.m_InitialState, dfa.m_Transitions);
    return commonApplyNaming(dfa, dfa.m_Transitions, nameMaping);
}


// --- Minimization -----------------------------------------------------------

DFA minimizeRemoveUseless(const DFA& dfa) {
    const map<Config, State>& trans = dfa.m_Transitions;

    map<State, set<State>> tracking;
    {
        queue<State> queue;
        queue.push(dfa.m_InitialState);
        set<State> visited;

        while(!queue.empty()) {
            const State state = queue.front();
            queue.pop();

            auto itr = trans.lower_bound({state, 0});

            for (; itr != trans.end() && get<0>(itr -> first) == state; ++itr) {
                const State target = itr -> second;
                tracking[target].emplace(state);

                if (visited.count(target) == 0) {
                    visited.emplace(target);
                    queue.push(target);
                }
            }
        }
    }
    set<State> useful = dfa.m_FinalStates;
    {
        queue<State> queue;
        for (const State fin : dfa.m_FinalStates)
            queue.push(fin);

        while(!queue.empty()) {
            const State state = queue.front();
            queue.pop();

            for (const State parent : tracking[state]) {
                if (useful.count(parent) == 0) {
                    useful.emplace(parent);
                    queue.push(parent);
                }
            }
        }
    }

    map<Config, State> newTransitions;
    for (const auto& [config, target] : dfa.m_Transitions) {
        if (useful.count(config.first) != 0 && useful.count(target) != 0 )
            newTransitions.emplace(make_pair(config, target));
    }

    useful.emplace(dfa.m_InitialState);

    return DFA {
        useful, dfa.m_Alphabet, newTransitions, dfa.m_InitialState, dfa.m_FinalStates
    };
}

using Group = State;
using CheckingResult = tuple<Group, vector<Group>, State>;
const State emptyGroup = (State) -1;

map<State, Group> minimizeCreateInitialLookup(const DFA& dfa) {
    const set<State>& states = dfa.m_States;
    const set<State>& fin = dfa.m_FinalStates;

    map<State, Group> lookup;

    for (const State state : states) {
        const Group group = fin.count(state) != 0;
        lookup.emplace(make_pair(state, group));
    }

    return lookup;
}

map<State, Group> minimizeCreateDerivedLookup(const DFA& dfa, const set<CheckingResult>& prev) {
    map<State, Group> lookup;
    Group nameCounter = 0;

    if (prev.empty()) return lookup;
    // insert the first row
    lookup.emplace(make_pair(get<2>(*prev.begin()), nameCounter));

    for (auto itr = ++prev.begin(), itrPrev = prev.begin(); itr != prev.end(); ++itr, ++itrPrev) {
        const State state = get<2>(*itr);
        if (get<0>(*itr) == get<0>(*itrPrev) &&
                get<1>(*itr) == get<1>(*itrPrev)) {
            lookup.emplace(make_pair(state, nameCounter));
        } else {
            lookup.emplace(make_pair(state, ++nameCounter));
        }
    }

    return lookup;
}

set<CheckingResult> minimizeFillInTrans(const DFA& dfa, const map<State, Group>& lookup) {
    const set<Symbol>& alphabet = dfa.m_Alphabet;
    const set<State>& states = dfa.m_States;
    const map<Config, State>& trans = dfa.m_Transitions;

    set<CheckingResult> result;

    for (const State state : states) {
        const Group group = lookup.at(state);
        vector<Group> mappedTrans;
        mappedTrans.reserve(alphabet.size());

        for (const Symbol symbol : alphabet) {
            const Config key = {state, symbol};
            const auto res = trans.find(key);

            if (res != trans.end() && states.count(res -> second) != 0) {
                mappedTrans.emplace_back(lookup.at(res -> second));
            } else {
                mappedTrans.emplace_back(emptyGroup);
            }
        }

        result.emplace(CheckingResult{group, mappedTrans, state});
    }
    return result;
}

DFA minimizeToAutomate(const DFA& dfa, const set<CheckingResult>& current) {
    const set<Symbol>& alphabet = dfa.m_Alphabet;
    const set<State>& fin = dfa.m_FinalStates;

    set<State> newStates;
    map<Config, State> newTrans;
    set<State> newFin;
    State newInitial = (State) -1;

    for (const auto& res : current) {
        const auto& [group, children, state] = res;
        newStates.emplace(group);

        auto alpItr = alphabet.begin();
        auto chItr = children.begin();

        for (; alpItr != alphabet.end(); ++alpItr, ++chItr) {
            const Group& child = *chItr;
            if (child != emptyGroup)
                newTrans.emplace(make_pair(Config{group, *alpItr}, child));
        }

        if (fin.count(state) != 0)
            newFin.emplace(group);
        if (dfa.m_InitialState == state)
            newInitial = group;
    }

    return DFA {
        newStates, dfa.m_Alphabet, newTrans, newInitial, newFin
    };
}

DFA minimizeEquiv(const DFA& dfa) {

    set<CheckingResult> prevState;
    set<CheckingResult> currentState;
    {
        const map<State, Group> lookup = minimizeCreateInitialLookup(dfa);
        prevState = minimizeFillInTrans(dfa, lookup);
    }


    while(true) {
        const map<State, Group> lookup = minimizeCreateDerivedLookup(dfa, prevState);
        currentState = minimizeFillInTrans(dfa, lookup);

        if (currentState == prevState) break;
        swap(currentState, prevState);
    }

    return minimizeToAutomate(dfa, currentState);
}

DFA minimize(const DFA& dfa) {
    // removeUnreachable - removed by prev algorithms
    const DFA& ready = minimizeRemoveUseless(dfa);
    return minimizeEquiv(ready);
}


// --- Parallel run -----------------------------------------------------------

using DoubleState = tuple<State, State>;
using DoubleConfig = tuple<DoubleState, Symbol>;

map<DoubleConfig, DoubleState> parallelRunTransitions(const DFA& dfa1, const DFA& dfa2) {
    const map<Config, State>& trans1 = dfa1.m_Transitions;
    const map<Config, State>& trans2 = dfa2.m_Transitions;
    const set<Symbol> alphabet = dfa1.m_Alphabet;

    map<DoubleConfig, DoubleState> transitions;

    queue<DoubleState> queue;
    queue.push({dfa1.m_InitialState, dfa2.m_InitialState});
    set<DoubleState> visited = {{dfa1.m_InitialState, dfa2.m_InitialState}};

    while(!queue.empty()) {
        const auto& state = queue.front();
        const auto [state1, state2] = state;

        auto itr1 = trans1.lower_bound({state1, 0});
        auto itr2 = trans2.lower_bound({state2, 0});
        // requires same alphabet and full automates
        for (const Symbol symbol : alphabet) {
            // next state
            const DoubleState target = {itr1 -> second, itr2 -> second};

            if (visited.find(target) == visited.end()) {
                visited.emplace(target);
                queue.push(target);
            }

            const DoubleConfig current = {state, symbol};
            transitions.emplace(make_pair(current, target));

            ++itr1; ++itr2;
        }

        queue.pop();
    }
    return transitions;
}

bool parallelRunAddInFinal(
        const DFA& dfa1,
        const DFA& dfa2,
        const DoubleState& state,
        const bool isIntersect
        ) {
    const set<State>& fin1 = dfa1.m_FinalStates;
    const set<State>& fin2 = dfa2.m_FinalStates;

    // checks if the state is final
    if (isIntersect) {
        return (fin1.count(get<0>(state)) && fin2.count(get<1>(state)));
    } else {
        return (fin1.count(get<0>(state)) || fin2.count(get<1>(state)));
    }
}

/**
 * Renames nodes according to the previously generated mapping 
 * and creates the finite notes set. Puts it all into the final DFA */
DFA parallelRunApplyNaming(
        const DFA& dfa1,
        const DFA& dfa2,
        const map<DoubleConfig, DoubleState>& transitions,
        const map<DoubleState, State>& nameMaping,
        const bool isIntersect
        ) {

    // states are just integers in [0, n>
    set<State> newStates = {0}; // the initial state must be always presented
    for (size_t i = 0; i < nameMaping.size(); ++i)
        newStates.emplace(i);

    map<Config, State> newTransitions;
    set<State> newFinite;

    // make sure initial state is always present
    {
        const DoubleState initial = {dfa1.m_InitialState, dfa2.m_InitialState};
        if (parallelRunAddInFinal(dfa1, dfa2, initial, isIntersect))
            newFinite.emplace(nameMaping.at(initial));
    }

    for (const auto& transition : transitions) {
        const auto& [setConfig, dest] = transition;
        const auto [state, symbol] = setConfig;

        // extract names
        const State name = nameMaping.at(state);
        const Config key = Config{name, symbol};
        const State value = nameMaping.at(dest);

        // add to the final result
        newTransitions.emplace(make_pair(key, value));

        if (parallelRunAddInFinal(dfa1, dfa2, state, isIntersect))
            newFinite.emplace(name);
        if (parallelRunAddInFinal(dfa1, dfa2, dest, isIntersect))
            newFinite.emplace(value);
    }

    const DFA output = {
        newStates,
        dfa1.m_Alphabet,
        newTransitions,
        0,
        newFinite
    };

    return output;
}

/** Performs the parallel run algorithm
 * both automates must have the same alphabet
 * both automates must be full */
DFA parallelRun(const DFA& dfa1, const DFA& dfa2, const bool isIntersect) {
    const map<DoubleConfig, DoubleState> transitions = parallelRunTransitions(dfa1, dfa2);
    const map<DoubleState, State> nameMaping = nameStates({dfa1.m_InitialState, dfa2.m_InitialState}, transitions);
    return parallelRunApplyNaming(dfa1, dfa2, transitions, nameMaping, isIntersect);
}


// --- Full automat -----------------------------------------------------------

DFA makeFull(const DFA& dfa, const set<Symbol>& alphabet) {
    const State failState = dfa.m_States.size(); // last item + 1
    map<Config, State> transitions = dfa.m_Transitions;
    
    // exploiting that states are indexed from 0 to len - 1
    for (State state = 0; state < failState; ++state) {
        for (const Symbol symbol : alphabet) {
            const Config config = {state, symbol};
            if (transitions.find(config) == transitions.end()) {
                transitions.emplace(make_pair(config, failState));
            }
        }
    }

    // add transitions for the final state
    for (const Symbol symbol : alphabet) {
        const Config config = {failState, symbol};
        transitions.emplace(make_pair(config, failState));
    }

    set<State> newStates = dfa.m_States;
    newStates.emplace(failState);

    return DFA{
        newStates,
        alphabet,
        transitions,
        dfa.m_InitialState,
        dfa.m_FinalStates
    };
}

DFA makeFull(const DFA& dfa) {
    return makeFull(dfa, dfa.m_Alphabet);
}

// --- Determinization --------------------------------------------------------

using SetState = set<State>;
using SetConfig = tuple<SetState, Symbol>;

map<SetConfig, SetState> determinizeTransitions(const NFA& nfa) {
    map<SetConfig, SetState> createdTransitions;

    set<SetState> visited{{nfa.m_InitialState}};
    queue<SetState> queue;
    queue.push({nfa.m_InitialState});

    while (!queue.empty()) {
        const SetState& stateGroup = queue.front();

        // holds all the states we can get to for the symbol given
        map<Symbol, SetState> results;

        // iterate over all the nodes in state set
        for (const auto& state : stateGroup) {
            // iterate over all the symbols for the original state
            auto itr = nfa.m_Transitions.lower_bound({state, 0});

            for (; itr != nfa.m_Transitions.end() && get<0>(itr -> first) == state; ++itr) {
                const Symbol symbol = itr -> first.second;
                const SetState& targets = itr -> second;
                results[symbol].insert(targets.begin(), targets.end());
            }
        }

        // analyze the results
        for (const auto& res : results) {
            const SetConfig config = SetConfig(stateGroup, res.first);
            const SetState& target = res.second;

            // add into the final result, needs to be renamed
            createdTransitions.emplace(make_pair(config, target));

            // add into the next BFS pass
            if (visited.find(target) == visited.end()) {
                visited.emplace(stateGroup);
                queue.push(target);
            }
        }

        queue.pop();
    }

    return createdTransitions;
}

/**
 * Renames nodes according to the previously generated mapping 
 * and creates the finite notes set. Puts it all into the final DFA */
DFA determinizeApplyNaming(
        const NFA& nfa,
        const map<SetConfig, SetState>& transitions,
        const map<SetState, State>& nameMaping
        ) {

    // states are just integers in [0, n>
    set<State> newStates = {0}; // the initial state must be always presented
    for (size_t i = 0; i < nameMaping.size(); ++i)
        newStates.emplace(i);

    map<Config, State> newTransitions;
    set<State> newFinite;

    // make sure initial state is always present
    {
        const SetState initial = {nfa.m_InitialState};
        if (checkIntersect(initial, nfa.m_FinalStates))
            newFinite.emplace(nameMaping.at(initial));
    }

    for (const auto& transition : transitions) {
        const auto& [setConfig, dest] = transition;
        const auto [state, symbol] = setConfig;

        // extract names
        const State name = nameMaping.at(state);
        const Config key = Config{name, symbol};
        const State value = nameMaping.at(dest);

        // add to the final result
        newTransitions.emplace(make_pair(key, value));

        // checks if the state is final
        if (checkIntersect(state, nfa.m_FinalStates))
            newFinite.emplace(name);
        if (checkIntersect(dest, nfa.m_FinalStates))
            newFinite.emplace(value);
    }

    const DFA output = {
        newStates,
        nfa.m_Alphabet,
        newTransitions,
        0,
        newFinite
    };

    return output;
}

/** Determinizes an automat */
DFA determinize(const NFA& nfa) {
    const map<SetConfig, SetState> transitions = determinizeTransitions(nfa);
    const map<SetState, State> naming = nameStates(SetState({nfa.m_InitialState}), transitions);
    return determinizeApplyNaming(nfa, transitions, naming);
}

DFA handleProgtest(const NFA& nfa1, const NFA& nfa2, const bool isIntersect) {
    const set<Symbol> alphabet = commonAlphabet<NFA>(nfa1, nfa2);
    const DFA dfa1 = makeFull(determinize(nfa1), alphabet);
    const DFA dfa2 = makeFull(determinize(nfa2), alphabet);
    return minimize(parallelRun(dfa1, dfa2, isIntersect));
}

DFA unify    (const NFA& a, const NFA& b) { return handleProgtest(a, b, false); }
DFA intersect(const NFA& a, const NFA& b) { return handleProgtest(a, b, true ); }

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b) {
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

void tests();

int main(void) {
    tests();
    return 0;
}

void separator(const string& str, ostream& out = cout) {
    out << "--- " << str << " ";
    for (ssize_t i = 0; i < 80 - 5 - (ssize_t) str.length(); ++i)
        out << "-";
    out << endl;
}

void print(const DFA& dfa, ostream& out = cout) {
    out <<
        dfa.m_States << "\n" <<
        dfa.m_Alphabet << "\n" <<
        dfa.m_Transitions << "\n" <<
        dfa.m_InitialState << "\n" <<
        dfa.m_FinalStates << endl;
}

void printCommon(const DFA& dfa, ostream& out = cout) {
    const DFA aut = commonNaming(dfa);
    print(aut);
}

void printDeterminization(const NFA& nfa1, const NFA& nfa2, const DFA& dfa) {
    const DFA d1 = determinize(nfa1);
    const DFA f1 = makeFull(d1);
    const DFA d2 = determinize(nfa2);
    const DFA f2 = makeFull(d2);
    const DFA in = parallelRun(f1, f2, true);
    const DFA un = parallelRun(f1, f2, false);
    const DFA us = minimizeRemoveUseless(in);
    const DFA mn = minimize(in);

    separator("A1");
    print(d1);

    separator("A1 complete");
    print(f1);

    separator("A2");
    print(d2);

    separator("A2 complete");
    print(f2);

    separator("Intersect ");
    print(in);

    separator("Union ");
    print(un);

    separator("Useless ");
    printCommon(us);

    separator("Minimal");
    print(mn);

    separator("Minimal common");
    printCommon(mn);

    separator("Reference");
    printCommon(dfa);
}

void testA() {
    separator("TEST A");

    NFA a1{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0, 1}},
            {{0, 'b'}, {0}},
            {{1, 'a'}, {2}},
        },
        0,
        {2},
    };
    NFA a2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA a{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{3, 'b'}, {3}},
            {{4, 'a'}, {2}},
            {{4, 'b'}, {3}},
        },
        0,
        {2},
    };

    printDeterminization(a1, a2, a);
    assert(commonNaming(a) == a);
    assert(commonNaming(intersect(a1, a2)) == a);

    cout << "\n\n\n" << flush;
}

void testB() {
    separator("TEST B");

    NFA b1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA b2{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'b'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{4, 'a'}, {4}},
            {{4, 'b'}, {4}},
        },
        0,
        {4},
    };
    DFA b{
        {0, 1, 2, 3, 4, 5, 6, 7, 8},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {3}},
            {{2, 'b'}, {4}},
            {{3, 'a'}, {5}},
            {{3, 'b'}, {6}},
            {{4, 'a'}, {7}},
            {{4, 'b'}, {4}},
            {{5, 'a'}, {5}},
            {{5, 'b'}, {4}},
            {{6, 'a'}, {8}},
            {{6, 'b'}, {4}},
            {{7, 'a'}, {5}},
            {{7, 'b'}, {4}},
            {{8, 'a'}, {8}},
            {{8, 'b'}, {8}},
        },
        0,
        {1, 5, 8},
    };

    printDeterminization(b1, b2, b);

    assert(commonNaming(b) == b);
    assert(commonNaming(unify(b1, b2)) == b);
    cout << "\n\n\n" << flush;
}

void testC() {
    separator("TEST C");

    NFA c1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA c2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0}},
            {{0, 'b'}, {0, 1}},
            {{1, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA c{
        {0},
        {'a', 'b'},
        {},
        0,
        {},
    };

    printDeterminization(c1, c2, c);

    assert(commonNaming(c) == c);
    assert(commonNaming(intersect(c1, c2)) == c);

    cout << "\n\n\n" << flush;
}

void testD() {
    separator("TEST D");

    NFA d1{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {2}},
            {{0, 'k'}, {1, 2, 3}},
            {{0, 'q'}, {0, 3}},
            {{1, 'i'}, {1}},
            {{1, 'k'}, {0}},
            {{1, 'q'}, {1, 2, 3}},
            {{2, 'i'}, {0, 2}},
            {{3, 'i'}, {3}},
            {{3, 'k'}, {1, 2}},
        },
        0,
        {2, 3},
    };
    NFA d2{
        {0, 1, 2, 3},
        {'i', 'k'},
        {
            {{0, 'i'}, {3}},
            {{0, 'k'}, {1, 2, 3}},
            {{1, 'k'}, {2}},
            {{2, 'i'}, {0, 1, 3}},
            {{2, 'k'}, {0, 1}},
        },
        0,
        {2, 3},
    };
    DFA d{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {1}},
            {{0, 'k'}, {2}},
            {{2, 'i'}, {3}},
            {{2, 'k'}, {2}},
            {{3, 'i'}, {1}},
            {{3, 'k'}, {2}},
        },
        0,
        {1, 2, 3},
    };

    printDeterminization(d1, d2, d);

    assert(commonNaming(d) == d);
    assert(commonNaming(intersect(d1, d2)) == d);

    cout << "\n\n\n" << flush;
}

void tests() {
    testA();
    testB();
    testC();
    testD();
}
#endif
