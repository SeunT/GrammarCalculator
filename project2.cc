/*
 * Copyright (C) Oluwaseun Talabi, 2020
 *       
 * Do not share this file with anyone
 * 
 */
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#include <algorithm>
#include<set>
#include <map>
#include "lexer.h"

using namespace std;

std::vector<std::pair<string, bool>> BigOsUniverse;
int predictive = 0;
std::vector < std::pair<int, set<int>>> setfirst;
std::vector < std::pair<int, set<int>>> followset;
std::vector<string> NontermsA;
std::vector<string> NontermsB;
std::vector<string> terms;
string startsymbol;
int lhs;
int index;
std::vector<int> rhs;
std::set<int> rhs1;
std::vector<std::pair<string, bool>>::iterator iter;
LexicalAnalyzer lexer;
bool reachable = false;
bool change;


struct left_right {
    int lhs;
    vector<int> rhs;
    bool use;
};
struct condition1_struc {
    int lhs;
    set<int> rhs1;
};

//has to be declared after the structure since it uses it
vector<left_right> rules;
vector<left_right> first_rules;
vector<condition1_struc> condition1;
std::vector<int> c1vec;
Token peek()
{
    Token t = lexer.GetToken();
    lexer.UngetToken(t);
    return t;

}

struct ExistsInVector
{
    ExistsInVector(const std::vector<string>& vec) : BigOsVec(vec) {
    }
    bool operator() (string i) {
        return (std::find(BigOsVec.begin(), BigOsVec.end(), i) != BigOsVec.end());
    }
private:
    const std::vector<string>& BigOsVec;
};

bool exists(const vector<string>& v, const string& name) {
    return std::find(v.begin(), v.end(), name) != v.end();
}
void syntax_error()
{
    cout << "SYNTAX ERROR !!!\n";
    exit(1);
}

//get first of the lhs rule
//if first at index 0 is a terminal then add it into first of lhs
//if first at index 0 is a nonterminal get the first of the nonterminal
//if first at index 0 is epsilon then get the first of the next index on rhs
void initialize_first_set() {
    setfirst.at(0).second.insert(0);
    for (int i = 1; i < setfirst.size(); i++)
    {
        bool check;
        check = exists(terms, BigOsUniverse.at(i).first.c_str());
        if (check) {
            setfirst.at(i).second.insert(i);
        }
    }

}
void initialize_follow_set() {

    followset.at(1).second.insert(1);
    followset.at(2).second.insert(1);
    for (int i = 3; i < followset.size(); i++)
    {
        bool check;
        check = exists(terms, BigOsUniverse.at(i).first.c_str());
        if (check) {
            followset.at(i).second.insert(i);
        }

    }

}
void first_set(int f, int r) {


    int right = first_rules.at(f).rhs.at(r);
    int left = first_rules.at(f).lhs;
    //length of right hand side
    int last_element = first_rules.at(f).rhs.size() - 1;

    for (set<int>::const_iterator p = setfirst.at(right).second.begin(); p != setfirst.at(right).second.end(); ++p) {

        const bool is_in = setfirst.at(left).second.find(*p) != setfirst.at(left).second.end();

        //condition1-----
        if (*p != 0)
            condition1[f].rhs1.insert(*p);
        //---------------
        if (!is_in && *p != 0) {
            setfirst.at(left).second.insert(*p);
            change = true;
        }

    }
    const bool is_in = setfirst.at(right).second.find(0) != setfirst.at(right).second.end();
    if (is_in && r < last_element) {

        first_set(f, r + 1);

    }
    else if (is_in && r == last_element) {

        const bool init = setfirst.at(left).second.find(0) != setfirst.at(left).second.end();

        if (!init) {
            //condition1-----------------
            condition1[f].rhs1.insert(0);
            //---------------------------
            setfirst.at(left).second.insert(0);
            change = true;
        }
    }

}
void follow_set(int f, int r, int right_most) {

    //gets the index of the right hand side element in universe
    int right = first_rules.at(f).rhs.at(r);
    //gets index of the element after the right hand side element in universe
    int rightmost = first_rules.at(f).rhs.at(right_most);
    //left hand side rule
    int left = first_rules.at(f).lhs;
    //length of right hand side
    int last_element = first_rules.at(f).rhs.size() - 1;

    if (r == last_element) {

        for (set<int>::const_iterator p = followset.at(left).second.begin(); p != followset.at(left).second.end(); ++p) {
            const bool is_in = followset.at(right).second.find(*p) != followset.at(right).second.end();
            if (!is_in) {
                followset.at(right).second.insert(*p);
                change = true;
            }
        }

    }
    else {
        for (set<int>::const_iterator p = setfirst.at(rightmost).second.begin(); p != setfirst.at(rightmost).second.end(); ++p) {

            const bool is_in = followset.at(right).second.find(*p) != followset.at(right).second.end();
            if (!is_in && *p != 0)
            {

                followset.at(right).second.insert(*p);
                change = true;
            }

        }

        const bool is_in = setfirst.at(rightmost).second.find(0) != setfirst.at(rightmost).second.end();

        if (is_in && right_most < last_element) {

            follow_set(f, r, right_most + 1);

        }
        else if (is_in && right_most == last_element) {
            for (set<int>::const_iterator p = followset.at(left).second.begin(); p != followset.at(left).second.end(); ++p) {
                const bool is_in = followset.at(right).second.find(*p) != followset.at(right).second.end();
                if (!is_in) {
                    followset.at(right).second.insert(*p);
                    change = true;
                }
            }
        }
    }

}
// read grammar
Token expect(TokenType expected_type)
{
    Token t = lexer.GetToken();
    if (t.token_type != expected_type)
        syntax_error();
    return t;
}
void initialize() {
    string s;
    bool check;

    //loop through every element in the universe

    for (int i = 0; i < BigOsUniverse.size(); i++) {
        //if the element is a terminal initialize it to true
        s = BigOsUniverse.at(i).first.c_str();
        check = exists(terms, s);
        if (check) {
            BigOsUniverse.at(i).second = true;
        }

    }
    change = true;
}
void initalize_reachable() {

    for (int i = 0; i < BigOsUniverse.size(); i++) {
        if (BigOsUniverse[i].first.c_str() == startsymbol) {
            BigOsUniverse[i].second = true;
        }
        else
            BigOsUniverse[i].second = false;
    }


}

void idlist() {
    Token t;
    bool check, check2;


    t = peek();

    iter = std::find(BigOsUniverse.begin(), BigOsUniverse.end(), make_pair(t.lexeme, false));
    size_t index = std::distance(BigOsUniverse.begin(), iter);
    rhs.push_back(index);
    //store in vectors for task 1



    if (t.token_type == ID) {

        check = exists(terms, t.lexeme);
        if (!check) {
            terms.push_back(t.lexeme);
            check2 = exists(NontermsB, t.lexeme);
            if (!check2) {

                BigOsUniverse.push_back(make_pair(t.lexeme, false));



                NontermsB.push_back(t.lexeme);
            }
        }
    }
    //task1^

    expect(ID);
    t = lexer.GetToken();
    if (t.token_type == ID)
    {
        //lexer.UngetToken(t);
        //return;

        lexer.UngetToken(t);
        idlist();
    }
    else if (t.token_type == HASH) {
        //lexer.UngetToken(t);
        //idlist();

        lexer.UngetToken(t);
        return;
    }
    else
    {
        syntax_error();
    }
}

void right_hand_side() {
    Token t;


    t = peek();
    if (t.token_type == ID) {
        // rhs.push_back(0);
        // return;

        idlist();
    }
    else if (t.token_type == HASH) {


        rhs.push_back(0);
        return;

        // return;
    }
    else {
        syntax_error();
    }

}
void rule() {
    Token t;
    bool check, check2;

    t = peek();


    iter = std::find(BigOsUniverse.begin(), BigOsUniverse.end(), make_pair(t.lexeme, false));
    size_t index = std::distance(BigOsUniverse.begin(), iter);
    lhs = index;


    check = exists(NontermsA, t.lexeme);
    //store in to vectors for task1

    if (!check) {

        NontermsA.push_back(t.lexeme);

        check2 = exists(NontermsB, t.lexeme);
        if (!check2) {

            BigOsUniverse.push_back(make_pair(t.lexeme, false));
            NontermsB.push_back(t.lexeme);
        }

    }
    //task1^

    expect(ID);
    expect(ARROW);
    right_hand_side();
    expect(HASH);

    rules.push_back({ lhs,rhs,false });
    first_rules.push_back({ lhs,rhs,false });
    rhs.clear();
}
void ruleslist() {

    Token t;
    rule();
    t = lexer.GetToken();

    if (t.token_type == ID) {
        lexer.UngetToken(t);
        ruleslist();
    }
    else if (t.token_type == DOUBLEHASH) {
        lexer.UngetToken(t);
        return;
    }





}
void find_useful_symbols() {

    bool check, change2 = true;

    startsymbol = BigOsUniverse.at(rules[0].lhs).first.c_str();
    while (change) {
        int change1 = 0;
        change = false;
        for (int i = 0; i < rules.size(); i++) {

            if (rules[i].use == false) {

                //proof by contradicition

                rules[i].use = true;
                for (int j = 0; j < rules[i].rhs.size(); j++) {

                    if (BigOsUniverse.at(rules[i].rhs.at(j)).second == false) {
                        //BigOsUniverse.at(rules.at(i).lhs).second = false;
                        rules[i].use = false;
                        change = false;
                        break;
                    }
                    else {
                        change = true;
                    }
                }
            }

            if (change == true) {
                BigOsUniverse.at(rules.at(i).lhs).second = true;
                change1 += 1;
            }

        }
        if (change1 > 0)
            change = true;

    }
    //get rid of all the rules that are false in the rule list

    for (int i = 0; i < rules.size(); i++) {
        while (rules[i].use == false) {
            predictive++;
            rules.erase(rules.begin() + i);
            if (rules.size() == 0 || rules.size() == i) {
                break;
            }
        }
    }

}
void find_reachable_set() {
    bool change_reach = true;

    //see if the set is even reachable if the sets not reachable the start symbol has been deleted from the rules set
    for (int i = 0; i < rules.size(); i++) {
        if (startsymbol == BigOsUniverse.at(rules[i].lhs).first.c_str()) {
            reachable = true;

        }
        //change all rules to false to be checked if they are reachable later.
        rules[i].use = false;
    }
    if (!reachable) {
        return;
    }
    initalize_reachable();

    while (change_reach) {
        change_reach = false;

        for (int i = 0; i < rules.size(); i++) {

            if (BigOsUniverse.at(rules.at(i).lhs).second == true) {
                rules[i].use = true;

                for (int j = 0; j < rules[i].rhs.size(); j++) {
                    //check if its a non terminal first
                    bool check;
                    check = exists(NontermsA, BigOsUniverse.at(rules[i].rhs.at(j)).first.c_str());
                    if (check) {
                        if (BigOsUniverse.at(rules[i].rhs.at(j)).second == false) {
                            BigOsUniverse.at(rules[i].rhs.at(j)).second = true;
                            change_reach = true;
                        }
                    }

                }
            }

        }
    }

    //erase unreachables from rule list
    for (int i = 0; i < rules.size(); i++) {
        while (rules[i].use == false) {
            predictive++;
            rules.erase(rules.begin() + i);
            if (rules.size() == 0 || rules.size() == i) {

                break;
            }

        }
    }

}

void ReadGrammar()
{

    BigOsUniverse.push_back(make_pair("#", true));
    BigOsUniverse.push_back(make_pair("$", false));

    ruleslist();
    expect(DOUBLEHASH);

    terms.erase(std::remove_if(terms.begin(), terms.end(), ExistsInVector(NontermsA)), terms.end());
    NontermsB.erase(std::remove_if(NontermsB.begin(), NontermsB.end(), ExistsInVector(terms)), NontermsB.end());

    for (int i = 0; i < BigOsUniverse.size(); i++) {
        setfirst.push_back(make_pair(i, set<int>{}));
        followset.push_back(make_pair(i, set<int>{}));

    }

    initialize_first_set();
    initialize_follow_set();
    initialize();

}

// Task 1
void printTerminalsAndNoneTerminals()
{


    for (auto i : terms) {
        cout << i << " ";
    }
    for (auto j : NontermsB) {
        cout << j << " ";
    }

}

// Task 2
void RemoveUselessSymbols()
{

    find_useful_symbols();
    find_reachable_set();

    if (rules.size() > 0) {
        if (reachable) {
            for (int i = 0; i < rules.size(); i++) {

                string s = BigOsUniverse.at(rules.at(i).lhs).first.c_str();
                cout << s << " " << "-> ";

                for (int j = 0; j < rules[i].rhs.size(); j++)
                {
                    string b = BigOsUniverse.at(rules[i].rhs.at(j)).first.c_str();
                    cout << b << " ";

                }
                cout << "\n";
            }
        }
    }

}
void find_firstset() {
    //initialize condition1  rules of firsts
    for (int i = 0; i < first_rules.size(); i++) {
        condition1.push_back({ first_rules[i].lhs, {} });
    }

    change = true;
    while (change) {
        change = false;
        for (int i = 0; i < first_rules.size(); i++) {

            first_set(i, 0);

        }
    }
}
// Task 3
void CalculateFirstSets()
{
    find_firstset();

    for (int i = 0; i < setfirst.size(); i++) {
        bool check = exists(NontermsA, BigOsUniverse.at(setfirst.at(i).first).first);

        string s = BigOsUniverse.at(setfirst.at(i).first).first;

        if (check) {

            cout << "FIRST(" + s + ")" + " = { ";
            set<int>::const_iterator it = setfirst.at(i).second.begin();
            int num = setfirst.at(i).second.size();
            if (setfirst.at(i).second.size() == 0) {
                cout << " }";
                cout << "\n";
            }
            else
            {
                for (int j = 0; j < num; j++) {
                    string b = BigOsUniverse.at(*it).first;
                    if (j == num - 1) {
                        first_rules.push_back({ lhs,rhs,false });
                        cout << b << " }";
                        cout << "\n";
                    }
                    else {

                        cout << b << ", ";
                    }
                    it++;
                }
            }
        }


    }


}
void find_followset() {
    change = true;
    while (change) {
        change = false;
        for (int i = 0; i < first_rules.size(); i++) {
            int size = first_rules[i].rhs.size();
            for (int j = 0; j < size; j++)
            {
                bool check = exists(NontermsA, BigOsUniverse.at(first_rules[i].rhs.at(j)).first.c_str());
                if (check) {
                    if (j == size - 1) {
                        follow_set(i, j, 0);
                    }
                    else
                    {
                        follow_set(i, j, j + 1);

                    }
                }
            }
        }
    }
}
// Task 4
void CalculateFollowSets()
{
    find_firstset();
    find_followset();


    for (int i = 0; i < followset.size(); i++) {
        bool check = exists(NontermsA, BigOsUniverse.at(setfirst.at(i).first).first);

        string s = BigOsUniverse.at(setfirst.at(i).first).first;

        if (check) {
            cout << "FOLLOW(" + s + ")" + " = { ";
            set<int>::const_iterator it = followset.at(i).second.begin();
            int num = followset.at(i).second.size();
            if (followset.at(i).second.size() == 0) {
                cout << " }";
                cout << "\n";
            }
            else
            {
                for (int j = 0; j < num; j++) {
                    string b = BigOsUniverse.at(*it).first;
                    if (j == num - 1) {
                        cout << b << " }";
                        cout << "\n";
                    }
                    else {

                        cout << b << ", ";
                    }
                    it++;
                }
            }


        }


    }
}

// Task 5
void CheckIfGrammarHasPredictiveParser()
{
    int c1left;

    find_useful_symbols();
    find_reachable_set();
    find_firstset();
    find_followset();
    bool condition_1 = true;
    bool condition2 = true;
    //condition1
    for (int i = 0; i < condition1.size(); i++) {

        for (int j = i + 1; j < condition1.size(); j++) {
            if (condition1[i].lhs == condition1[j].lhs) {
                for (set<int>::const_iterator p = condition1.at(i).rhs1.begin(); p != condition1.at(i).rhs1.end(); ++p) {
                    const bool init1 = condition1.at(j).rhs1.find(*p) != condition1.at(j).rhs1.end();
                    if (init1) {
                        condition_1 = false;
                    }
                }
            }

        }
    }


    //condition2
    for (int i = 0; i < setfirst.size(); i++) {
        bool check = exists(NontermsA, BigOsUniverse.at(i).first.c_str());
        if (check) {
            const bool is_in = setfirst.at(i).second.find(0) != setfirst.at(i).second.end();
            if (is_in) {
                for (set<int>::const_iterator p = followset.at(i).second.begin(); p != followset.at(i).second.end(); ++p) {
                    const bool init = setfirst.at(i).second.find(*p) != setfirst.at(i).second.end();
                    if (init) {
                        condition2 = false;
                    }
                }
            }
        }
    }
    if (predictive > 0) {
        cout << "NO";
    }
    else if (condition_1 && condition2) {
        cout << "YES";
    }
    else {
        cout << "NO";
    }
}

int main(int argc, char* argv[])
{
    int task;

    if (argc < 2)
    {
        cout << "Error: missing argument\n";
        return 1;
    }

    /*
       Note that by convention argv[0] is the name of your executable,
       and the first argument to your program is stored in argv[1]
     */

    task = atoi(argv[1]);


    ReadGrammar();  // Reads the input grammar from standard input
                    // and represent it internally in data structures
                    // ad described in project 2 presentation file

    switch (task) {
    case 1: printTerminalsAndNoneTerminals();
        break;

    case 2: RemoveUselessSymbols();
        break;

    case 3: CalculateFirstSets();
        break;

    case 4: CalculateFollowSets();
        break;

    case 5: CheckIfGrammarHasPredictiveParser();
        break;

    default:
        cout << "Error: unrecognized task number " << task << "\n";
        break;
    }
    return 0;
}

