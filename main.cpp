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

    bool is_lambda() const{
        return this->representation == "lambda";
    }

    bool is_eof() const{
        return this->representation == "$";
    }

    bool operator<(const Symbol &other) const {
        return this->representation < other.representation;
    }

    bool operator==(const Symbol &other) const {
        return this->representation == other.representation;
    }

    bool operator!=(const Symbol &other) const {
        return this->representation != other.representation;
    }
};

std::ostream& operator<<(std::ostream& os, const Symbol& sym) {
    os << sym.representation;
    return os;
}

struct Rule {
    Symbol lhs;
    std::vector<Symbol> rhs;

    bool operator==(const Rule &other) const {
        return (this->lhs == other.lhs) && (this->rhs == other.rhs);
    }
};

// lga15
// TOKENTYPE and srcValue
struct Token {
    std::string type;
    std::string srcValue;
};

// lga15
// Simple parse tree node, just a symbol with a list of children
struct ParseNode {
    Symbol symbol;
    std::vector<ParseNode*> children;
};

// lga15
// Reads tokens from a file and lets the parser go through them
class TokenStream {
private:
    std::vector<Token> tokens;
    size_t index = 0;

public:
    TokenStream(const std::string& path) {
        std::ifstream infile(path);
        if (!infile) {
            std::cerr << "Error opening token file\n";
            exit(1);
        }

        std::string line;
        while (std::getline(infile, line)) {
            if (line.empty()) {
                continue;
            }

            std::istringstream iss(line);
            Token tok;
            iss >> tok.type;

            if (!(iss >> tok.srcValue)) {
                tok.srcValue = "";
            }

            tokens.push_back(tok);
        }

        // Add EOF token at the end so the parser knows when input is finished
        tokens.push_back(Token{"$", ""});
    }

    Token peek() const {
        if (index < tokens.size()) {
            return tokens[index];
        }
        return Token{"$", ""};
    }

    void advance() {
        if (index < tokens.size()) {
            index++;
        }
    }
};

class Grammar {
public:
    std::set<Symbol> symbols;
    std::set<Symbol> nonterminals;
    std::set<Symbol> terminals;
    std::vector<Rule> rules;
    std::vector<std::set<Symbol>> predictSets;
    std::map<Symbol, std::vector<Rule>> productions_to;
    std::map<Symbol, std::vector<Rule>> productions_from;
    std::set<Symbol> derives_to_lambda_set;
    std::map<Symbol, std::set<Symbol>> symbol_first_set;
    Symbol start_symbol;
    std::set<Symbol> jointPredictSets;
    std::map<Symbol,std::map<Symbol,uint>> parsingTable;

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

        for (const auto &rul : rules){
            predictSets.push_back(getPredictSet(rul));
        }
        jointPredictSets = getJoint();
        makeParsingTable();
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
                    for (size_t j = gamma; j < rule.rhs.size(); j++) {
                        pi.push_back(rule.rhs[j]);
                    }

                    if (pi.size() > 0) {
                        std::set<Symbol> ns;
                        std::set<Symbol> G = first_set(pi, ns);
                        for (Symbol symb : G) {
                            if (!sym.is_lambda()) f.insert(symb);
                        }
                    }

                    bool all_nonterminals_and_derive_to_lambda = true;
                    for(Symbol &symb : pi) {
                        if (!nonterminals.count(symb) || !derives_to_lambda_set.count(symb)) {
                            all_nonterminals_and_derive_to_lambda = false;
                            break;
                        }
                    }

                    if (all_nonterminals_and_derive_to_lambda) {
                        std::set<Symbol> G = follow_set(rule.lhs, T);
                        for (Symbol symb : G) {
                            if (!sym.is_lambda()) f.insert(symb);
                        }
                    }
                }
            }

        }

        return f;
    }

    std::set<Symbol> first_set(
        const std::vector<Symbol>& sequ,
        std::set<Symbol>& T
    ) {
        std::vector<Symbol> seq(sequ);
        Symbol x = seq[0];
        for (size_t i = 0; i < seq.size() - 1; i++) {
            seq[i] = seq[i + 1];
        }
        seq.pop_back();

        if (terminals.count(x)) {
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
                    if (!sym.is_lambda()) f.insert(sym);
                }
            }
        }

        if (derives_to_lambda_set.count(x) && !seq.empty()) {
            std::set<Symbol> G = first_set(seq, T);
            for (Symbol sym : G) {
                if (!sym.is_lambda()) f.insert(sym);
            }
        }

        return f;
    }

    bool derives_to_lambda(const Symbol sym, std::vector<Rule> &t) {
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
            for (Symbol &symb : rule.rhs) {
                if (!nonterminals.count(symb)) {
                    flag_continue = true;
                    break;
                }
            }
            if (flag_continue) {
                continue;
            }

            bool all_derive_lambda = true;
            for (Symbol &symb : rule.rhs) {
                t.push_back(rule);
                all_derive_lambda = derives_to_lambda(symb, t);
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

    // lga15
    // Builds a parse tree starting from the grammar's start symbol and uses the LL(1) parsing table to decide which production to use
    ParseNode* buildParseTree(TokenStream& ts) {
        ParseNode* root = parseSymbol(start_symbol, ts);

        if (root == nullptr) {
            return nullptr;
        }

        Symbol lookahead{ts.peek().type};

        return root;
    }

    // lga15
    // Prints the parse tree in an indented format
    void printParseTree(ParseNode* node, int depth = 0) const {
        if (node == nullptr) {
            return;
        }

        for (int i = 0; i < depth; i++) {
            std::cout << "   ";
        }
        std::cout << node->symbol << "\n";

        for (ParseNode* child : node->children) {
            printParseTree(child, depth + 1);
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

    std::set<Symbol> getPredictSet(const Rule &rule){
        std::set<Symbol> t;
        std::set<Symbol> out(first_set(rule.rhs,t));
        for (const auto &s : rule.rhs){
            if (!s.is_lambda() && derives_to_lambda_set.find(s) == derives_to_lambda_set.end()) return out;
        }
        t.clear();
        std::set<Symbol> out2(follow_set(rule.lhs,t));
        out.insert(out2.begin(),out2.end());
        return out;
    }

    std::set<Symbol> getJoint() const{
        std::set<Symbol> out;
        for (uint i=0;i<predictSets.size()-1; ++i){
            for (uint j=i+1;j<predictSets.size(); ++j){
                if (rules[i].lhs != rules[j].lhs || out.find(rules[i].lhs) != out.end()) continue;
                auto it1 = predictSets[i].begin();
                auto it2 = predictSets[j].begin();

                while (it1 != predictSets[i].end() && it2 != predictSets[j].end()) {
                    if (*it1 < *it2) {
                        ++it1;
                    } else if (*it2 < *it1) {
                        ++it2;
                    } else {
                        std::cout << rules[i].lhs << '\n';
                        out.insert(rules[i].lhs); // Found a common element
                        break;
                    }
                }
            }
        }
        return out;
    }

    void makeParsingTable(){
        for (uint i(0); i<predictSets.size();++i){
            for (const auto &s : predictSets[i]){
                parsingTable[rules[i].lhs][s] = i;
            }
        }
    }

    // lga15
    // If the symbol is:
    // lambda -> make a lambda node
    // terminal -> match against current input token
    // nonterminal -> use parsing table to choose the correct rule
    ParseNode* parseSymbol(const Symbol& sym, TokenStream& ts) {
        ParseNode* node = new ParseNode{sym, {}};

        // lambda is represented as a leaf node
        if (sym.is_lambda()) {
            return node;
        }

        // If this is a terminal or EOF, it must match the current token
        if (terminals.count(sym) || sym.is_eof()) {
            Symbol lookahead{ts.peek().type};

            if (sym == lookahead) {
                ts.advance();
                return node;
            } else {
                std::cerr << "Parse error: expected " << sym
                          << " but found " << lookahead << "\n";
                delete node;
                return nullptr;
            }
        }

        // Otherwise this is a nonterminal, so consult the LL(1) parsing table
        Symbol lookahead{ts.peek().type};

        if (parsingTable.count(sym) == 0 || parsingTable.at(sym).count(lookahead) == 0) {
            std::cerr << "Parse error: no parsing table entry for ("
                      << sym << ", " << lookahead << ")\n";
            delete node;
            return nullptr;
        }

        uint ruleIndex = parsingTable.at(sym).at(lookahead);
        const Rule& rule = rules[ruleIndex];

        // Expand the nonterminal using the selected rule
        for (const Symbol& rhsSym : rule.rhs) {
            ParseNode* child = parseSymbol(rhsSym, ts);
            if (child == nullptr) {
                delete node;
                return nullptr;
            }
            node->children.push_back(child);
        }

        return node;
    }
};

int main(int argc, char* argv[]) {
    // lga15
    // Now expects two command line arguments: the grammar file and the token file.
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <grammar file> <token file>\n";
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

    std::cout << "symbols:\n";
    for (auto a : g.symbols) {
        std::cout<<a.representation<<" ";
        std::cout<<(g.derives_to_lambda_set.count(a) > 0)<<"\n";
    }

    std::cout << "terminals S:\n";
    for (auto a : g.terminals) {
        std::cout << a << ' ';
    }
    std::cout << '\n';

    std::cout << "nonterminals S:\n";
    for (auto a : g.nonterminals) {
        std::cout << a << ' ';
    }
    std::cout << '\n';

    std::cout << "first_set S:\n";
    std::vector<Symbol> seq = {Symbol{"S"}};
    auto st = std::set<Symbol>();
    for (auto a : g.first_set(seq, st)) {
        std::cout << a.representation << ' ';
    }
    std::cout << '\n';
    
    std::cout << "follow_set A:\n";
    st = std::set<Symbol>();
    for (auto a : g.follow_set(Symbol{"A"}, st)) {
        std::cout << a.representation << ' ';
    }
    std::cout << '\n';

    std::cout << "Pred Sets:\n";
    for (const auto &ps : g.predictSets) {
        for (const auto &p : ps) {
            std::cout << p << ' ';
        }
        std::cout << '\n';
    }

    std::cout << "Joint Pred Sets:\n";
    for (const auto &ps : g.jointPredictSets) {
        std::cout << ps << ' ';
    }
    std::cout << '\n';

    std::cout << "Pred Sets:\n";
    for (const auto &row : g.parsingTable) {
        std::cout << row.first << ' ';
        for (const auto &p : row.second) {
            std::cout << p.first << ':' << p.second << ' ';
        }
        std::cout << '\n';
    }

    // lga15
    // Build the parse tree from the token stream using the LL(1) parsing table.
    TokenStream ts(argv[2]);
    ParseNode* root = g.buildParseTree(ts);

    // lga15
    // Print the parse tree
    if (root != nullptr) {
        std::cout << "Parse Tree:\n";
        g.printParseTree(root);
    }

    return 0;
}
