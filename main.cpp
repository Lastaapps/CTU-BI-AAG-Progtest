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
ostream& operator<<(ostream& out, const pair<T1, T2>& pair);
template<typename T>
ostream& operator<<(ostream& out, const set<T>& set);
template<typename T1, typename T2>
ostream& operator<<(ostream& out, const map<T1, T2>& map);

template<typename T1, typename T2>
ostream& operator<<(ostream& out, const pair<T1, T2>& pair) {
    return out << "<" << pair.first << " " << pair.second << ">";
}

template<typename T>
ostream& operator<<(ostream& out, const set<T>& set) {
    out << "[";
    for (const auto& item: set)
        out << (item == *set.begin() ? "" : " ") << item;
    return out << "]";
}

template<typename T1, typename T2>
ostream& operator<<(ostream& out, const map<T1, T2>& map) {
    out << "{";
    for (const auto& item: map)
        out << (item == *map.begin() ? "" : " ")
            << "(" << item.first << " " << item.second << ")";
    return out << "}";
}

void print(const DFA& dfa, ostream& out = cout) {
    out <<
        dfa.m_States << "\n" <<
        dfa.m_Alphabet << "\n" <<
        dfa.m_Transitions << "\n" <<
        dfa.m_InitialState << "\n" <<
        dfa.m_FinalStates << endl;
}

#endif

using SetState = set<State>;
using SetConfig = pair<SetState, Symbol>;

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

// --- Full automat -----------------------------------------------------------

DFA makeFull(const DFA& dfa) {
    const State failState = dfa.m_States.size(); // last item + 1
    map<Config, State> transitions = dfa.m_Transitions;
    
    // exploiting that states are indexed from 0 to len - 1
    for (size_t state = 0; state < failState; ++state) {
        for (const Symbol symbol : dfa.m_Alphabet) {
            const Config config = {state, symbol};
            if (transitions.find(config) == transitions.end()) {
                transitions.emplace(make_pair(config, failState));
            }
        }
    }

    // add transitions for the final state
    for (const Symbol symbol : dfa.m_Alphabet) {
        const Config config = {failState, symbol};
        transitions.emplace(make_pair(config, failState));
    }

    SetState newStates = dfa.m_States;
    newStates.emplace(failState);

    return DFA{
        newStates,
        dfa.m_Alphabet,
        transitions,
        dfa.m_InitialState,
        dfa.m_FinalStates
    };
}

// --- Determinization --------------------------------------------------------

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

            for (; itr != nfa.m_Transitions.end() && itr -> first.first == state; ++itr) {
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

/** Creates a mapping for SetState -> State */
map<SetState, State> determinizeNameStates(
        const NFA& nfa,
        const map<SetConfig, SetState>& transitions
        ) {
    map<SetState, State> nameMaping;

    // starts at 0
    State nextStateName = 0;
    set<SetState> visited = {{nfa.m_InitialState}};
    queue<SetState> queue;
    queue.push({nfa.m_InitialState});

    // BFS
    while (!queue.empty()) {
        const State name = nextStateName++;
        const SetState& state = queue.front();

        // add to the final result
        nameMaping.emplace(make_pair(state, name));

        // adds other to queue in lexicographical order
        auto itr = transitions.lower_bound({state, 0});
        for (; itr != transitions.end() && itr -> first.first == state; ++itr) {
            const SetState& targets = itr -> second;
            if (visited.find(targets) == visited.end()) {
                visited.emplace(state);
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
DFA determinizeApplyNaming(
        const NFA& nfa,
        const map<SetConfig, SetState>& transitions,
        const map<SetState, State>& nameMaping
        ) {

    // states are just integers in [0, n>
    set<State> newStates;
    for (size_t i = 0; i < nameMaping.size(); ++i)
        newStates.emplace(i);

    map<Config, State> newTransitions;
    set<State> newFinite;

    for (const auto& transition : transitions) {
        const auto& [setConfig, dest] = transition;
        const auto& [state, symbol] = setConfig;

        // extract names
        const State name = nameMaping.at(state);
        const Config key = Config{name, symbol};
        const State value = nameMaping.at(dest);

        // add to the final result
        newTransitions.emplace(make_pair(key, value));

        // checks if the state is final
        if (checkIntersect(state, nfa.m_FinalStates))
            newFinite.emplace(name);
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
    map<SetConfig, SetState> transitions = determinizeTransitions(nfa);
    map<SetState, State> naming = determinizeNameStates(nfa, transitions);
    return determinizeApplyNaming(nfa, transitions, naming);
}

DFA unify(const NFA& a, const NFA& b);
DFA intersect(const NFA& a, const NFA& b);

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b) {
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

int tests();

int main(void) {

    // tests();
    return 0;
}

/*int tests() {
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
    assert(intersect(a1, a2) == a);

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
    assert(unify(b1, b2) == b);

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
    assert(intersect(c1, c2) == c);

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
    assert(intersect(d1, d2) == d);
}*/
#endif
