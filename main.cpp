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

    bool is_lambda() const {
        return this->representation == "lambda";
    }

    bool is_eof() const {
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

using ParseKey = std::pair<Symbol, Symbol>;
using ParseTable = std::map<ParseKey, Rule>;

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
        }

        bool lambda_is_symbol = false;
        for (Rule &rule : rules) {
            for (Symbol &sym : rule.rhs) {
                productions_to[sym].push_back(rule);
                if (sym.is_eof()) start_symbol = rule.lhs;
                if (sym.is_lambda()) lambda_is_symbol = true;
                if (!sym.is_lambda() && !(nonterminals.count(sym))) {
                    terminals.insert(sym);
                    productions_to[sym].push_back(rule);
                } 
            }
        }

        for (Symbol sym : terminals)
            symbols.insert(sym);
        for (Symbol sym : nonterminals)
            symbols.insert(sym);

        if(lambda_is_symbol) {
            symbols.insert(Symbol{"lambda"});
        }

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
                    gamma = i + 1;
                    std::vector<Symbol> pi;
                    for (size_t i = gamma; i < rule.rhs.size(); i++) {
                        pi.push_back(rule.rhs[i]);
                    }

                    if (pi.size() > 0) {
                        std::set<Symbol> ns;
                        std::vector<Symbol> pi_copy = pi;
                        std::set<Symbol> G = first_set(pi_copy, ns);
                        for (Symbol sym : G) {
                            if (!sym.is_lambda()) {
                                f.insert(sym);
                            }
                        }
                    }

                    bool all_nonterminals_and_derive_to_lambda = true;
                    for(Symbol &sym : pi) {
                        if (!nonterminals.count(sym) || !derives_to_lambda_set.count(sym)) {
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
            }

        }

        return f;
    }

    std::set<Symbol> first_set(
        std::vector<Symbol>& seq,
        std::set<Symbol>& T
    ) {
        if (seq.empty()) {
            return {};
        }

        Symbol x = seq[0];
        for (size_t i = 0; i < seq.size() - 1; i++) {
            seq[i] = seq[i + 1];
        }
        seq.pop_back();

        if (!nonterminals.count(x)) {
            std::set<Symbol> s;
            s.insert({x});
            return s;
        }

        std::set<Symbol> f;
        if (!T.count(x)) {
            T.insert(x);
            for (Rule &rule : productions_from[x]) {
                std::vector<Symbol> rhs_copy = rule.rhs;
                std::set<Symbol> G = first_set(rhs_copy, T);
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
                if (!nonterminals.count(sym)) {
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
        return false;
    }

    std::set<Symbol> predict_set(Rule& rule) {
        std::set<Symbol> ps;

        std::vector<Symbol> rhs = rule.rhs;
        std::set<Symbol> visited;
        std::set<Symbol> first = first_set(rhs, visited);

        for (const Symbol& sym : first) {
            if (!sym.is_lambda()) {
                ps.insert(sym);
            }
        }

        bool derives_lambda = false;
        if (rule.rhs.size() == 1 && rule.rhs[0].is_lambda()) {
            derives_lambda = true;
        } else {
            derives_lambda = true;
            for (const Symbol& sym : rule.rhs) {
                if (sym.is_lambda()) {
                    continue;
                }
                if (!nonterminals.count(sym) || !derives_to_lambda_set.count(sym)) {
                    derives_lambda = false;
                    break;
                }
            }
        }

        if (derives_lambda) {
            std::set<Symbol> follow = follow_set(rule.lhs, std::set<Symbol>());
            for (const Symbol& sym : follow) {
                if (!sym.is_lambda()) {
                    ps.insert(sym);
                }
            }
        }

        return ps;
    }

    bool pairwise_disjoint() {
        for (const Symbol& nt : nonterminals) {
            const std::vector<Rule>& productions = productions_from[nt];

            for (size_t i = 0; i < productions.size(); i++) {
                Rule r1 = productions[i];
                std::set<Symbol> p1 = predict_set(r1);

                for (size_t j = i + 1; j < productions.size(); j++) {
                    Rule r2 = productions[j];
                    std::set<Symbol> p2 = predict_set(r2);

                    for (const Symbol& sym : p1) {
                        if (p2.count(sym)) {
                            return false;
                        }
                    }
                }
            }
        }

        return true;
    }

    ParseTable build_ll1_table(bool& is_ll1) {
        ParseTable table;
        is_ll1 = true;

        for (Rule& rule : rules) {
            std::set<Symbol> ps = predict_set(rule);

            for (const Symbol& lookahead : ps) {
                ParseKey key = {rule.lhs, lookahead};

                auto it = table.find(key);
                if (it != table.end() && !(it->second == rule)) {
                    is_ll1 = false; // rule conflict in cell, not ll1
                } else {
                    table[key] = rule;
                }
            }
        }

        return table;
    }

    void print_ll1_table() {
        bool is_ll1;
        ParseTable table = build_ll1_table(is_ll1);

        if (is_ll1) {
            std::cout << "Grammar is LL(1)" << std::endl;
        } else {
            std::cout << "Grammar is not LL(1)" << std::endl;
        }

        for (const auto& entry : table) {
            const Symbol& lhs = entry.first.first;
            const Symbol& lookahead = entry.first.second;
            const Rule& rule = entry.second;

            std::cout << "[" << lhs.representation << ", " << lookahead.representation << "] = "
                << rule.lhs.representation << " -> ";

            for (const auto& sym : rule.rhs) {
                std::cout << sym.representation << " ";
            }
            std::cout << std::endl;
        }
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

    std::cout << "Rules:\n";
    for (auto r : g.rules) {
        std::cout << r.lhs.representation << " -> ";
        for (auto sym : r.rhs) {
            std::cout<<sym.representation<<" ";
        }
        std::cout<<'\n';
    }

    std::cout << "Symbols / derives to lambda\n";
    for (auto a : g.symbols) {
        std::cout<<a.representation<<" ";
        std::cout<<(g.derives_to_lambda_set.count(a) > 0)<<"\n";
    }

    std::cout << "First(B)\n";
    std::vector<Symbol> seq = {Symbol{"B"}};
    auto st = std::set<Symbol>();
    for (auto a : g.first_set(seq, st)) {
        std::cout << a.representation << "\n";
    }

    std::cout << "Follow(B)\n";
    st = std::set<Symbol>();
    for (auto a : g.follow_set(Symbol{"B"}, st)) {
        std::cout << a.representation << "\n";
    }

    std::string disjoint;
    if (g.pairwise_disjoint()) {
        disjoint = "yes";
    } else {
        disjoint = "no";
    }

    std::cout << "\nPairwise disjoint predict sets: " << disjoint << "\n\n";

    g.print_ll1_table();

    return 0;
}
