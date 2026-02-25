#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <map>

struct Rule {
    std::string lhs;
    std::vector<std::string> rhs;
};

bool is_nonterminal(const std::string& s) {
    for (char c : s) {
        if (c >= 'A' && c <= 'Z') {
            return true;
        }
    }
    return false;
}

std::set<std::string> get_nt(const std::vector<Rule>& rules) {
    std::set<std::string> nts;
    for (const Rule& r : rules) {
        nts.insert(r.lhs);
    }
    return nts;
}

std::set<std::string> compute_nullable_set(const std::vector<Rule>& rules) {
    std::set<std::string> nullable;

    for (const Rule& r : rules) {
        if (r.rhs.empty()) {
            nullable.insert(r.lhs);
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;

        for (const Rule& r : rules) {
            if (nullable.count(r.lhs)) continue;

            if (r.rhs.empty()) {
                if (nullable.insert(r.lhs).second) changed = true;
                continue;
            }

            bool all_nullable = true;
            for (const std::string& sym : r.rhs) {
                if (!is_nonterminal(sym)) {
                    all_nullable = false;
                    break;
                }
                if (!nullable.count(sym)) {
                    all_nullable = false;
                    break;
                }
            }

            if (all_nullable) {
                if (nullable.insert(r.lhs).second) changed = true;
            }
        }
    }

    return nullable;
}

std::string find_start_symbol(const std::vector<Rule>& rules) {
    for (const Rule& r : rules) {
        for (const std::string& sym : r.rhs) {
            if (sym == "$") {
                return r.lhs;
            }
        }
    }
    if (!rules.empty()) return rules[0].lhs;
    return "";
}

std::map<std::string, std::set<std::string>> compute_first_sets(const std::vector<Rule>& rules) {
    std::set<std::string> nonterminals = get_nt(rules);
    std::set<std::string> nullable = compute_nullable_set(rules);

    std::map<std::string, std::set<std::string>> first;
    for (const std::string& nt : nonterminals) {
        first[nt] = std::set<std::string>();
    }

    bool changed = true;
    while (changed) {
        changed = false;

        for (const Rule& r : rules) {
            const std::string& A = r.lhs;

            if (r.rhs.empty()) {
                if (first[A].insert("lambda").second) {
                    changed = true;
                }
                continue;
            }

            bool all_nullable_prefix = true;

            for (size_t i = 0; i < r.rhs.size(); i++) {
                const std::string& X = r.rhs[i];

                if (!is_nonterminal(X)) {
                    if (first[A].insert(X).second) {
                        changed = true;
                    }
                    all_nullable_prefix = false;
                    break;
                } else {
                    for (const std::string& t : first[X]) {
                        if (t == "lambda") continue;
                        if (first[A].insert(t).second) {
                            changed = true;
                        }
                    }

                    if (!nullable.count(X)) {
                        all_nullable_prefix = false;
                        break;
                    }
                }
            }

            if (all_nullable_prefix) {
                if (first[A].insert("lambda").second) {
                    changed = true;
                }
            }
        }
    }

    return first;
}

std::set<std::string> first_of_sequence(const std::vector<std::string>& seq, size_t start_index, const std::map<std::string, std::set<std::string>>& first, const std::set<std::string>& nullable) {
    std::set<std::string> out;

    if (start_index >= seq.size()) {
        out.insert("lambda");
        return out;
    }

    bool all_nullable = true;

    for (size_t i = start_index; i < seq.size(); i++) {
        const std::string& X = seq[i];

        if (!is_nonterminal(X)) {
            out.insert(X);
            all_nullable = false;
            break;
        }

        auto it = first.find(X);
        if (it != first.end()) {
            for (const std::string& t : it->second) {
                if (t == "lambda") continue;
                out.insert(t);
            }
        }

        if (!nullable.count(X)) {
            all_nullable = false;
            break;
        }
    }

    if (all_nullable) {
        out.insert("lambda");
    }

    return out;
}

std::map<std::string, std::set<std::string>> compute_follow_sets(const std::vector<Rule>& rules, const std::map<std::string, std::set<std::string>>& first) {
    std::set<std::string> nonterminals = get_nt(rules);
    std::set<std::string> nullable = compute_nullable_set(rules);
    std::string start_symbol = find_start_symbol(rules);

    std::map<std::string, std::set<std::string>> follow;
    for (const std::string& nt : nonterminals) {
        follow[nt] = std::set<std::string>();
    }

    if (!start_symbol.empty()) {
        follow[start_symbol].insert("$");
    }

    bool changed = true;
    while (changed) {
        changed = false;

        for (const Rule& r : rules) {
            const std::string& A = r.lhs;

            for (size_t i = 0; i < r.rhs.size(); i++) {
                const std::string& B = r.rhs[i];

                if (!is_nonterminal(B)) continue;

                std::set<std::string> first_beta = first_of_sequence(r.rhs, i + 1, first, nullable);

                for (const std::string& t : first_beta) {
                    if (t == "lambda") continue;
                    if (follow[B].insert(t).second) {
                        changed = true;
                    }
                }

                if (first_beta.count("lambda")) {
                    for (const std::string& t : follow[A]) {
                        if (follow[B].insert(t).second) {
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    return follow;
}

std::string concat_except_last(std::vector<std::string> input) {
    std::string contents = "";
    for (size_t i = 0; i < (input.size() - 1); i++) {
        contents += input[i];
    }
    return contents;
}



std::vector<std::string> split(const std::string& s, const std::string& delimiter) {
    std::vector<std::string> result;
    size_t start = 0;
    size_t end = s.find(delimiter);

    while (end != std::string::npos) {
        result.push_back(s.substr(start, end - start));
        start = end + delimiter.length();
        end = s.find(delimiter, start);
    }

    result.push_back(s.substr(start));
    return result;
}

std::vector<std::string> split_ws(const std::string& s) {
    std::istringstream iss(s);
    std::vector<std::string> out;
    for (std::string tok; iss >> tok; ) out.push_back(tok);
    return out;
}

bool nullable(std::string nonterminal, std::vector<struct Rule> rules) {
    for (auto rule : rules) {
        if (rule.lhs == nonterminal) {
            if (rule.rhs.empty()) {
                return true;
            }
        }
    }
    return false;
}

std::map<std::string, std::vector<std::vector<std::string>>> vec2map(std::vector<struct Rule> rules) {
    std::map<std::string, std::vector<std::vector<std::string>>> map;
    for (auto rule : rules) {
        if (map.find(rule.lhs) == map.end()) {
            std::vector<std::vector<std::string>> temp;
            temp.push_back(rule.rhs);
            map[rule.lhs] = temp;
        } else {
            map[rule.lhs].push_back(rule.rhs);
        }
    }
    return map;
}

std::set<std::string> getAllSymbols(std::vector<struct Rule> rules) {
    std::set<std::string> symbols;

    for (auto rule : rules) {
        symbols.insert(rule.lhs);
        symbols.insert(rule.rhs.begin(), rule.rhs.end());
    }

    return symbols;
}


int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <filename>\n";
        return 1;
    }

    std::ifstream infile(argv[1]);
    if (!infile) {
        std::cerr << "Error opening file\n";
        return 1;
    }

    std::string contents = "";

    std::string line;
    while (std::getline(infile, line)) {
        contents += line;
        contents += " ";
    }

    auto wss = split_ws(contents);

    std::vector<struct Rule> rules; 

    bool expecting_lhs = true;
    std::string current_lhs;
    std::vector<std::string> current_alternative;

    int i = 0;
    while (i < wss.size()) {
        if (expecting_lhs) {
            current_lhs = wss[i];
            expecting_lhs = false;
            i += 2;
            continue;
        } 

        if (i + 1 < wss.size() && wss[i+1] == "->") {
            rules.push_back(Rule{current_lhs, current_alternative});
            current_alternative.clear();
            current_lhs.clear();
            expecting_lhs = true;
            continue;
        }

        if (wss[i] == "|") {
            rules.push_back(Rule{current_lhs, current_alternative});
            current_alternative.clear();
        } else if (wss[i] == "lambda") {

        } else {
            current_alternative.push_back(wss[i]);
        }
        
        i++;
    }

    if (!expecting_lhs) {
        rules.push_back(Rule{current_lhs, current_alternative});
    }

    int y = 0;
    for (auto item : rules) {
        std::cout << "(" << y << ") ";
        std::cout << item.lhs << " -> ";
        for (auto item2 : item.rhs) {
            std::cout << item2 << " ";
        }
        std::cout << std::endl;
        y++;
    }

    std::cout << "Start Symbol: " << find_start_symbol(rules) << std::endl; 

    return 0;
}