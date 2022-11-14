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

struct NFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

#endif

DFA unify(const NFA& a, const NFA& b);
DFA intersect(const NFA& a, const NFA& b);

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

int main()
{
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
}
#endif
