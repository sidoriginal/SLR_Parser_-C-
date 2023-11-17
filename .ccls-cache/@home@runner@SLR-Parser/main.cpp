#include <bits/stdc++.h>
using namespace std;

struct Augmented_Grammar {
  char lhs;
  string rhs;
  bool operator<(const Augmented_Grammar &other) const {
    if (lhs == other.lhs) {
      return rhs < other.rhs;
    }
    return lhs < other.lhs;
  }
  bool operator==(const Augmented_Grammar &other) const {
    return lhs == other.lhs && rhs == other.rhs;
  }
};

struct trans {
  set<Augmented_Grammar> from;
  set<Augmented_Grammar> to;
  char symbol;
  bool operator<(const trans &other) const {
    if (symbol < other.symbol)
      return true;
    if (symbol > other.symbol)
      return false;
    if (from < other.from)
      return true;
    if (other.from < from)
      return false;
    return to < other.to;
  }
};

class DFA {
public:
  set<trans> transitions;
  set<set<Augmented_Grammar>> final_state;
  set<Augmented_Grammar> start_state;
  DFA() {}
  void set_transitions(set<Augmented_Grammar> f, set<Augmented_Grammar> s,
                       char symb) {
    trans new_trans;
    new_trans.from = f;
    new_trans.to = s;
    new_trans.symbol = symb;
    transitions.insert(new_trans);
  }

  void set_final_state(set<Augmented_Grammar> f) { final_state.insert(f); }

  void set_start_state(set<Augmented_Grammar> s) { start_state = s; }

  set<set<Augmented_Grammar>> get_final_state() { return final_state; }

  set<Augmented_Grammar> get_start_state() { return start_state; }
  void display(set<pair<int, set<Augmented_Grammar>>> LR_items_named) {
    for (auto i : transitions) {
      cout << "================================================================"
              "================"
           << endl;
      string type = "Shift";
      int id;
      if (final_state.find(i.from) != final_state.end()) {
        type = "Reduce";
      }
      for (auto x : LR_items_named) {
        if (x.second == i.from) {
          id = x.first;
          break;
        }
      }
      cout << "(" << type << " Type With ID I" << id << ": )" << endl;
      cout << "From: " << endl;
      for (auto j : i.from) {
        cout << j.lhs << "->";
        cout << j.rhs << "\n";
      }
      type = "Shift";
      if (final_state.find(i.to) != final_state.end()) {
        type = "Reduce";
      }
      for (auto x : LR_items_named) {
        if (x.second == i.to) {
          id = x.first;
          break;
        }
      }
      cout << "(" << type << " Type With ID I" << id << ": )" << endl;
      cout << "To: " << endl;
      for (auto j : i.to) {
        cout << j.lhs << "->";
        cout << j.rhs << "\n";
      }
      cout << "With Symbol: ";
      cout << i.symbol << endl;
    }
  }
  void getnamed(set<pair<int, set<Augmented_Grammar>>> &LR_items_named) {
    map<set<Augmented_Grammar>, int> itemToIdMap;
    int nextId = 0;

    for (auto &transition : transitions) {
      if (itemToIdMap.find(transition.from) == itemToIdMap.end()) {
        itemToIdMap[transition.from] = nextId++;
      }
      if (itemToIdMap.find(transition.to) == itemToIdMap.end()) {
        itemToIdMap[transition.to] = nextId++;
      }
    }

    for (auto &item : itemToIdMap) {
      LR_items_named.insert({item.second, item.first});
    }
  }
};

void computeFirstSet(char non_terminal, const vector<Augmented_Grammar> &AG,
                     map<char, unordered_set<char>> &FIRST_set,
                     const set<char> &non_terminals,
                     const set<char> &terminals) {
  if (FIRST_set.find(non_terminal) != FIRST_set.end())
    return;
  FIRST_set[non_terminal] = {};
  for (const auto &prod : AG) {
    if (prod.lhs == non_terminal) {
      if (terminals.find(prod.rhs[0]) != terminals.end() ||
          prod.rhs[0] == '^') {
        FIRST_set[non_terminal].insert(prod.rhs[0]);
      } else {
        for (char symbol : prod.rhs) {
          if (non_terminals.find(symbol) != non_terminals.end()) {
            computeFirstSet(symbol, AG, FIRST_set, non_terminals, terminals);
            FIRST_set[non_terminal].insert(FIRST_set[symbol].begin(),
                                           FIRST_set[symbol].end());
            if (FIRST_set[symbol].find('^') == FIRST_set[symbol].end()) {
              break;
            }
          } else {
            FIRST_set[non_terminal].insert(symbol);
            break;
          }
        }
      }
    }
  }
}

void computeFollowSet(char non_terminal, const vector<Augmented_Grammar> &AG,
                      map<char, unordered_set<char>> &FOLLOW_set,
                      const map<char, unordered_set<char>> &FIRST_set,
                      const set<char> &non_terminals,
                      const set<char> &terminals) {
  if (non_terminal == 'W') {
    FOLLOW_set[non_terminal].insert('$');
  }
  for (const auto &prod : AG) {
    string rhs = prod.rhs;
    for (size_t i = 0; i < rhs.length(); ++i) {
      if (rhs[i] == non_terminal) {
        if (i + 1 < rhs.length()) {
          char next_symbol = rhs[i + 1];
          if (terminals.find(next_symbol) != terminals.end()) {
            FOLLOW_set[non_terminal].insert(next_symbol);
          } else {
            for (char symbol : FIRST_set.at(next_symbol)) {
              if (symbol != '^') {
                FOLLOW_set[non_terminal].insert(symbol);
              }
            }
            if (FIRST_set.at(next_symbol).find('^') !=
                FIRST_set.at(next_symbol).end()) {
              for (char symbol : FOLLOW_set[prod.lhs]) {
                FOLLOW_set[non_terminal].insert(symbol);
              }
            }
          }
        } else {
          for (char symbol : FOLLOW_set[prod.lhs]) {
            FOLLOW_set[non_terminal].insert(symbol);
          }
        }
      }
    }
  }
}

set<Augmented_Grammar>
computeDFA(DFA &dfa, const vector<Augmented_Grammar> AG, queue<char> expand,
           unordered_set<char> vis, const set<char> terminals,
           const set<char> non_terminals,
           set<pair<int, set<Augmented_Grammar>>> &LR_items, int id,
           vector<Augmented_Grammar> rec) {
  set<char> moves;
  set<Augmented_Grammar> temp;
  map<char, set<Augmented_Grammar>> mapping;
  char type = 'S';
  if (id == 0) {
    expand.push('S');
    Augmented_Grammar t;
    t.lhs = 'W';
    t.rhs = ".S";
    mapping['S'].insert(t);
    temp.insert(t);
  }

  for (auto item : rec) {
    char n_lhs = item.lhs;
    string n_rhs = item.rhs;

    size_t dot_index = n_rhs.find('.');
    if (dot_index != string::npos) {
      n_rhs.erase(dot_index, 1);
      if (dot_index + 1 <= n_rhs.length()) {
        n_rhs.insert(dot_index + 1, 1, '.');
        expand.push(n_rhs[dot_index + 2]);
        Augmented_Grammar t;
        t.lhs = n_lhs;
        t.rhs = n_rhs;
        mapping[n_rhs[dot_index + 2]].insert(t);
      } else {
        type = 'R';
      }
    }

    Augmented_Grammar t;
    t.lhs = n_lhs;
    t.rhs = n_rhs;
    temp.insert(t);
  }

  rec.clear();

  while (!expand.empty()) {
    char c = expand.front();
    expand.pop();
    if (terminals.find(c) == terminals.end() &&
        non_terminals.find(c) == non_terminals.end() && c != '^')
      continue;
    // cout << c << " is popped" << endl;

    // cout << "2 Size of expand: " << expand.size() << endl;
    moves.insert(c);
    if (non_terminals.find(c) != non_terminals.end() &&
        vis.find(c) == vis.end()) {
      for (int i = 0; i < AG.size(); i++) {
        string new_rhs = AG[i].rhs;
        if (AG[i].lhs == c) {
          new_rhs.insert(0, 1, '.');
          Augmented_Grammar A;
          A.lhs = c;
          A.rhs = new_rhs;
          mapping[new_rhs[1]].insert(A);
          expand.push(new_rhs[1]);
          // cout << new_rhs[1] << endl;
          // cout << "3 Size of expand: " << expand.size() << endl;
          Augmented_Grammar t;
          t.lhs = c;
          t.rhs = new_rhs;
          temp.insert(t);
        }
      }
    }
    vis.insert(c);
  }
  bool found = false;
  for (auto i : LR_items) {
    if (i.second == temp) {
      found = true;
      return temp;
    }
  }
  if (found == false) {
    // cout << "temp is: " << endl;
    for (auto k : temp) {
      // cout << k.lhs << "->" << k.rhs << endl;
    }
    LR_items.insert({id, temp});
    int new_id = id + 1;
    if (id == 0)
      dfa.set_start_state(temp);
    for (auto i : temp) {
      if (i.rhs[i.rhs.length() - 1] == '.') {
        dfa.set_final_state(temp);
        // cout<<"Its reducing"<<endl;
      }
    }

    for (auto i : moves) {
      // cout << "for move :  " << i << endl;
      vector<Augmented_Grammar> vec;
      for (auto j : mapping[i]) {
        vec.push_back(j);
        // cout << j.lhs << "->" << j.rhs << endl;
      }
      dfa.set_transitions(temp,
                          computeDFA(dfa, AG, {}, {}, terminals, non_terminals,
                                     LR_items, new_id++, vec),
                          i);
    }
  }
  return temp;
}

map<pair<int, char>, string> actionTable;
map<pair<int, char>, int> gotoTable;

unordered_set<char>
getFollowSet(char non_terminal,
             const map<char, unordered_set<char>> &FOLLOW_set) {
  auto it = FOLLOW_set.find(non_terminal);
  if (it != FOLLOW_set.end()) {
    return it->second;
  }
  return {};
}

void createActionGotoTables(
    DFA &dfa, const set<pair<int, set<Augmented_Grammar>>> &LR_items_named,
    const map<char, unordered_set<char>> &FOLLOW_set) {
  for (const auto &item : LR_items_named) {
    int state = item.first;
    const auto &lrItemSet = item.second;

    // Handling Shift and Goto
    for (const auto &trans : dfa.transitions) {
      if (trans.from == lrItemSet) {
        char symbol = trans.symbol;
        for (const auto &toItem : LR_items_named) {
          if (toItem.second == trans.to) {
            int toState = toItem.first;
            if (isupper(symbol)) { // Non-terminal
              gotoTable[{state, symbol}] = toState;
            } else { // Terminal
              actionTable[{state, symbol}] = "S" + to_string(toState);
            }
            break;
          }
        }
      }
    }

    // Handling Reduce
    for (const auto &lrItem : lrItemSet) {
      size_t dotPos = lrItem.rhs.find('.');
      if (dotPos != string::npos && dotPos == lrItem.rhs.size() - 1) {
        if (lrItem.lhs == 'W' && lrItem.rhs == "S.") {
          actionTable[{state, '$'}] = "ACC";
        } else {
          for (char symbol : getFollowSet(lrItem.lhs, FOLLOW_set)) {
            string production = lrItem.rhs.substr(0, lrItem.rhs.size() - 1);
            actionTable[{state, symbol}] =
                "R(" + string(1, lrItem.lhs) + "->" + production + ")";
          }
        }
      }
    }
  }
}

void displayTables() {
  cout << "Action Table:\n";
  for (const auto &entry : actionTable) {
    cout << "State " << entry.first.first << ", Symbol " << entry.first.second
         << " : " << entry.second << "\n";
  }

  cout << "\nGoto Table:\n";
  for (const auto &entry : gotoTable) {
    cout << "State " << entry.first.first << ", Symbol " << entry.first.second
         << " : " << entry.second << "\n";
  }
}

void parseString(const std::string &input, int initialState) {
  stack<int> states;
  states.push(initialState);

  string buffer = input + "$"; // Adding end symbol
  size_t index = 0;
  cout << "Initial State is: I" << initialState << endl;
  while (true) {

    int currentState = states.top();
    char currentSymbol = buffer[index];
    cout << "---String top is: " << currentSymbol << endl;
    cout << "---Stack top is: " << currentState << endl;
    if (actionTable.find({currentState, currentSymbol}) == actionTable.end()) {
      cout << "Error: No action defined for state " << currentState
           << " and symbol " << currentSymbol << ".\n";
      break;
    }

    string action = actionTable.at({currentState, currentSymbol});

    if (action[0] == 'S') { // Shift
      int nextState = std::stoi(action.substr(1));
      states.push(nextState);
      index++;
      cout << "Shift " << currentSymbol << ", move to state " << nextState
           << ".\n";
    } else if (action[0] == 'R') { // Reduce
      string production =
          action.substr(2, action.size() - 3); // Extract production rule
      char lhs = production[0];
      int rhsLength = production.size() -
                      3; // Length of the right-hand side of the production

      for (int i = 0; i < rhsLength; i++) {
        states.pop(); // Pop states for each symbol in the right-hand side
      }

      if (gotoTable.find({states.top(), lhs}) == gotoTable.end()) {
        cout << "Error: No goto state defined for state " << states.top()
             << " and symbol " << lhs << ".\n";
        break;
      }

      int nextState = gotoTable.at({states.top(), lhs});
      states.push(nextState);

      cout << "Reduce using " << production << ", move to state " << nextState
           << ".\n";
    } else if (action == "ACC") {
      cout << "String accepted.\n";
      break;
    } else {
      cout << "Invalid action: " << action << ".\n";
      break;
    }
  }
}

int main() {
  // Knowing number of production rules
  int n;
  cout << "Enter number of grammar rules: ";
  cin >> n;
  cout << endl;
  // Taking Production rules and augmenting the grammar
  vector<Augmented_Grammar> AG(n + 1);
  AG[0].lhs = 'W';
  AG[0].rhs = 'S';
  set<char> terminals;
  set<char> non_terminals;
  non_terminals.insert('W');
  for (int i = 1; i <= n; i++) {
    cout << "For grammar rule " << i << ": \nEnter lhs:";
    char lhs;
    cin >> lhs;
    AG[i].lhs = lhs;
    non_terminals.insert(lhs);
    cout << endl;
    cout << "Enter rhs:";
    string rhs;
    cin >> rhs;
    AG[i].rhs = rhs;
    for (int i = 0; i < rhs.size(); i++) {
      if (rhs[i] >= 'A' && rhs[i] <= 'Z') {
        non_terminals.insert(rhs[i]);
      } else {
        terminals.insert(rhs[i]);
      }
    }
    cout << endl;
  }
  // Printing the augmented grammar
  cout << "-------------------------------------------------------------------"
       << endl;
  cout << "Augmented Grammar: \n";
  for (int i = 0; i <= n; i++) {
    cout << AG[i].lhs << " -> " << AG[i].rhs << endl;
  }
  // Printing terminals and non-terminals
  cout << "-------------------------------------------------------------------"
       << endl;
  cout << "Terminals: ";
  for (auto i : terminals) {
    cout << i << ",";
  }
  cout << endl;
  cout << "Non-Terminals: ";
  for (auto i : non_terminals) {
    cout << i << ",";
  }
  cout << endl;

  // Finding FIRST set
  cout << "-------------------------------------------------------------------"
       << endl;
  map<char, unordered_set<char>> FIRST_set;
  for (char non_terminal : non_terminals) {
    computeFirstSet(non_terminal, AG, FIRST_set, non_terminals, terminals);
  }

  // Printing FIRST sets
  cout << "FIRST Sets: " << endl;
  for (const auto &fs : FIRST_set) {
    cout << "FIRST(" << fs.first << ") = { ";
    for (char symbol : fs.second) {
      cout << symbol << " ";
    }
    cout << "}" << endl;
  }

  // Finding FOLLOW set
  cout << "-------------------------------------------------------------------"
       << endl;
  map<char, unordered_set<char>> FOLLOW_set;
  bool added;
  do {
    added = false;
    for (char non_terminal : non_terminals) {
      size_t before_size = FOLLOW_set[non_terminal].size();
      computeFollowSet(non_terminal, AG, FOLLOW_set, FIRST_set, non_terminals,
                       terminals);
      size_t after_size = FOLLOW_set[non_terminal].size();
      if (before_size != after_size) {
        added = true;
      }
    }
  } while (added);

  // Printing FOLLOW sets
  cout << "FOLLOW Sets: " << endl;
  for (const auto &fs : FOLLOW_set) {
    cout << "FOLLOW(" << fs.first << ") = { ";
    for (char symbol : fs.second) {
      cout << symbol << " ";
    }
    cout << "}" << endl;
  }
  // Getting LR(0) items and making DFA of them
  cout << "-------------------------------------------------------------------"
       << endl;
  DFA dfa;
  set<pair<int, set<Augmented_Grammar>>> LR_items;
  queue<char> expand;
  unordered_set<char> vis;
  vector<Augmented_Grammar> vec;
  Augmented_Grammar x;
  x.lhs = 'W';
  x.rhs = "S";
  vec.push_back(x);
  set<Augmented_Grammar> dummy = computeDFA(dfa, AG, expand, vis, terminals,
                                            non_terminals, LR_items, 0, {});
  // Printing LR(0) items
  set<pair<int, set<Augmented_Grammar>>> LR_items_named;
  dfa.getnamed(LR_items_named);
  cout << "LR(0) Items: " << endl;
  for (auto item : LR_items_named) {
    cout << "(I" << item.first << ": ";
    set<Augmented_Grammar> temp = item.second;
    for (auto j : temp) {
      cout << j.lhs << " -> " << j.rhs << "\n";
    }
    cout << ')' << endl;
  }

  // Printing DFA
  cout << "-------------------------------------------------------------------"
       << endl;
  cout << "DFA: " << endl;

  dfa.display(LR_items_named);

  // Creating and displaying tables
  createActionGotoTables(dfa, LR_items_named, FOLLOW_set);
  displayTables();

  // Parsing the strings given by user
  set<Augmented_Grammar> startState = dfa.get_start_state();
  int initialState = -1;
  for (const auto &item : LR_items_named) {
    if (item.second == startState) {
      initialState = item.first;
      break;
    }
  }
  cout << "------------------------------------------------------------------"
          "-"<<endl;
  string input;
  while (true) {
    cout << "Enter a string to parse (or type 'stop' to exit): ";
    cin >> input;
    cout << endl;

    if (input == "stop") {
      break;
    }

    parseString(input, initialState);
  }
}