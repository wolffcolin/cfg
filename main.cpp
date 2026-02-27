#include <iostream>
#include <map>
#include <set>
#include <algorithm>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>

struct Symbol {
    std::string representation;

    bool is_lambda() {
        return this->representation == "lambda";
    }

    bool is_nonterminal() {
        for (char c: this->representation) {
            if (c >= 'A' && c <= 'Z') {
                return true;
            }
        }
        return false;
    }

    bool is_eof() {
        return this->representation == "$";
    }

    bool operator<(const Symbol &other) const {
        return this->representation < other.representation;
    }

    bool operator==(const Symbol &other) const {
        return this->representation == other.representation;
    }
};

struct Rule {
    Symbol lhs;
    std::vector<Symbol> rhs;

    bool operator==(const Rule &other) const {
        return (this->lhs == other.lhs) && (this->rhs == other.rhs);
    }
};

class Grammar {
public:
    std::set<Symbol> symbols;
    std::set<Symbol> nonterminals;
    std::set<Symbol> terminals;
    std::vector<Rule> rules;
    std::map<Symbol, std::vector<Rule>> productions_to;
    std::map<Symbol, std::vector<Rule>> productions_from;
    std::set<Symbol> derives_to_lambda_set;
    std::map<Symbol, std::set<Symbol>> symbol_first_set;
    Symbol start_symbol;

    Grammar(std::string path) {
        parse_rules(path);

        for (Rule &rule : rules) {
            nonterminals.insert(rule.lhs);
            productions_from[rule.lhs].push_back(rule);
            for (Symbol &sym : rule.rhs) {
                if (sym.is_eof()) {
                    start_symbol = rule.lhs;
                }
                
                if (sym.is_nonterminal()) {
                    nonterminals.insert(sym);
                    productions_to[sym].push_back(rule);
                } else {
                    terminals.insert(sym);
                }
            }
        }

        for (Symbol sym : nonterminals) 
            symbols.insert(sym);
        for (Symbol sym : terminals) 
            symbols.insert(sym);

        for (Symbol sym : nonterminals) {
            std::vector<Rule> stack;
            derives_to_lambda(sym, stack);
        }
    }

    std::set<Symbol> follow_set(
        Symbol sym,
        std::set<Symbol> T
    ){
        if (T.count(sym)) {
            std::set<Symbol> st;
            return st;
        }

        T.insert(sym);
        std::set<Symbol> f;
        for (Rule &rule : productions_to[sym]) {
            size_t gamma = 0;
            for (size_t i = 0; i < rule.rhs.size(); i++) {
                if (rule.rhs[i] == sym) {
                    gamma = i;
                    break;
                }
            }

            gamma++;
            std::vector<Symbol> pi;
            for (size_t i = gamma; i < rule.rhs.size(); i++) {
                pi.push_back(rule.rhs[gamma]);
            }

            if (pi.size() > 0) {
                std::set<Symbol> ns;
                std::set<Symbol> G = first_set(pi, ns);
                for (Symbol sym : G) {
                    f.insert(sym);
                }
            }

            bool all_nonterminals_and_derive_to_lambda = true;
            for(Symbol &sym : pi) {
                if (!sym.is_nonterminal() || !derives_to_lambda_set.count(sym)) {
                    all_nonterminals_and_derive_to_lambda = false;
                    break;
                }
            }

            if (all_nonterminals_and_derive_to_lambda) {
                std::set<Symbol> G = follow_set(rule.lhs, T);
                for (Symbol sym : G) {
                    f.insert(sym);
                }
            }
        }

        return f;
    }

    std::set<Symbol> first_set(
        std::vector<Symbol>& seq,
        std::set<Symbol>& T
    ) {
        Symbol x = seq[0];
        for (size_t i = 0; i < seq.size() - 1; i++) {
            seq[i] = seq[i + 1];
        }
        seq.pop_back();

        if (!x.is_nonterminal()) {
            std::set<Symbol> s;
            s.insert({x});
            return s;
        }

        std::set<Symbol> f;
        if (!T.count(x)) {
            T.insert(x);
            for (Rule &rule : productions_from[x]) {
                std::set<Symbol> G = first_set(rule.rhs, T);
                for (Symbol sym : G) {
                    f.insert(sym);
                }
            }
        }

        if (derives_to_lambda_set.count(x) && !seq.empty()) {
            std::set<Symbol> G = first_set(seq, T);
            for (Symbol sym : G) {
                f.insert(sym);
            }
        }

        return f;
    }

    bool derives_to_lambda(Symbol sym, std::vector<Rule> &t) {
        if (derives_to_lambda_set.count(sym)) {
            return derives_to_lambda_set.find(sym) != derives_to_lambda_set.end();
        }

        for (Rule &rule : productions_from[sym]) {
            // O(n) search; can be optimized with std::set
            if (std::find(t.begin(), t.end(), rule) != t.end()) {
                continue;
            }
            if (rule.rhs.size() == 1 && rule.rhs[0].is_lambda()) {
                derives_to_lambda_set.insert(sym);
                return true;
            }
            bool flag_continue = false;
            for (Symbol &sym : rule.rhs) {
                if (!sym.is_nonterminal()) {
                    flag_continue = true;
                    break;
                }
            }
            if (flag_continue) {
                continue;
            }

            bool all_derive_lambda = true;
            for (Symbol &sym : rule.rhs) {
                t.push_back(rule);
                all_derive_lambda = derives_to_lambda(sym, t);
                t.pop_back();
                if (!all_derive_lambda) {
                    break;
                }
            }
            if (all_derive_lambda) {
                derives_to_lambda_set.insert(sym);
                return true;
            }
        }
        derives_to_lambda_set.insert(sym);
        return false;
    }

private:
    void parse_rules(std::string path) {
        std::ifstream infile(path);
        if (!infile) {
            std::cerr << "Error opening file\n";
            exit(1);
        }

        std::string contents = "";

        std::string line;
        while (std::getline(infile, line)) {
            contents += line;
            contents += " ";
        }

        auto wss = split_ws(contents);

        bool expecting_lhs = true;
        Symbol current_lhs;
        std::vector<Symbol> current_alternative;

        size_t i = 0;
        while (i < wss.size()) {
            if (expecting_lhs) {
                current_lhs = Symbol{wss[i]};
                expecting_lhs = false;
                i += 2;
                continue;
            } 

            if (i + 1 < wss.size() && wss[i+1] == "->") {
                this->rules.push_back(Rule{current_lhs, current_alternative});
                current_alternative.clear();
                expecting_lhs = true;
                continue;
            }

            if (wss[i] == "|") {
                rules.push_back(Rule{current_lhs, current_alternative});
                current_alternative.clear();
            } else {
                current_alternative.push_back(Symbol{wss[i]});
            }
        
            i++;
        }

        if (!expecting_lhs) {
            rules.push_back(Rule{current_lhs, current_alternative});
        }
    }

    std::vector<std::string> split_ws(const std::string& s) {
        std::istringstream iss(s);
        std::vector<std::string> out;
        for (std::string tok; iss >> tok; ) out.push_back(tok);
        return out;
    }
};

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <filename>\n";
        return 1;
    }

    Grammar g(argv[1]);

    for (auto r : g.rules) {
        std::cout << r.lhs.representation << " -> ";
        for (auto sym : r.rhs) {
            std::cout<<sym.representation<<" ";
        }
        std::cout<<'\n';
    }

    for (auto a : g.symbols) {
        std::cout<<a.representation<<" ";
        std::cout<<(g.derives_to_lambda_set.count(a) > 0)<<"\n";
    }

    std::vector<Symbol> seq = {Symbol{"B"}};
    auto st = std::set<Symbol>();
    for (auto a : g.first_set(seq, st)) {
        std::cout << a.representation << "\n";
    }

    
    st = std::set<Symbol>();
    for (auto a : g.follow_set(Symbol{"B"}, st)) {
        std::cout << a.representation << "\n";
    }

    return 0;
}
