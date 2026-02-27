#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <algorithm>

struct Rule {
    std::string lhs;
    std::vector<std::string> rhs;
};

std::set<std::string> get_nt(const std::vector<Rule>& rules) {
    std::set<std::string> nts;
    for (const Rule& r : rules) {
        nts.insert(r.lhs);
    }
    return nts;
}

std::set<std::string> compute_nullable_set(const std::vector<Rule>& rules, const std::set<std::string> &nonTerminals) {
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
                if (nonTerminals.find(sym) == nonTerminals.end()) {
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

std::set<std::string> GetFirstSet(const std::vector<std::string> &input, const std::set<std::string> &terminals, const std::vector<struct Rule> &rules, const std::set<std::string> &nullableSet, std::set<std::string> &seenSet){
    if (input.size() < 1){
        return {};
    }
    if (terminals.find(input[0]) != terminals.end()){
        return {input[0]};
    }
    std::set<std::string> output;
    if (seenSet.find(input[0]) == seenSet.end()){
        seenSet.insert(input[0]);
        for (const auto &rul : rules){
            if (input[0] == rul.lhs){
                std::set<std::string> tmp = GetFirstSet(rul.rhs,terminals,rules,nullableSet,seenSet);
                output.insert(tmp.begin(),tmp.end());
            }
        }
    }
    if (nullableSet.find(input[0]) != nullableSet.end()){
        std::set<std::string> tmp = GetFirstSet(std::vector<std::string>(input.begin() + 1, input.end()),terminals,rules,nullableSet,seenSet);
        output.insert(tmp.begin(),tmp.end());
    }
    return output;
}

std::set<std::string> GetFollowSet(const std::string &input, const std::set<std::string> &terminals, const std::vector<struct Rule> &rules, const std::set<std::string> &nullableSet, std::set<std::string> &seenSet){
    if (seenSet.find(input) != seenSet.end()){
        return {};
    }
    seenSet.insert(input);
    std::set<std::string> output;
    for (const auto &rul : rules){
        auto at = std::find(rul.rhs.begin(), rul.rhs.end(), input); //in the rhs
        if (at != rul.rhs.end()){
            auto leftOver = std::vector<std::string>(at + 1, rul.rhs.end());
            if (std::distance(at, rul.rhs.end()) - 1 > 0){ //at the end
                std::set<std::string> tmp = GetFirstSet(leftOver,terminals,rules,nullableSet,seenSet);
                output.insert(tmp.begin(),tmp.end());
                //check if all remaining are non terminals and nullable
                bool allGood = 1;
                for (const auto &item : leftOver){
                    if (terminals.find(item) != terminals.end()){
                        allGood = 0;
                        break;
                    }
                    else if (nullableSet.find(item) == nullableSet.end()){
                        allGood = 0;
                        break;
                    }
                }
                if (allGood){
                    tmp = GetFollowSet(rul.lhs,terminals,rules,nullableSet,seenSet);
                    output.insert(tmp.begin(),tmp.end());
                }
            }
            else{
                std::set<std::string> tmp = GetFollowSet(rul.lhs,terminals,rules,nullableSet,seenSet);
                output.insert(tmp.begin(),tmp.end());
            }
        }
    }


    return output;
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
    if (argc != 2) {
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
    std::set<std::string> nonTerminals;
    std::set<std::string> terminals;
    std::set<std::string> nullableSet;
    std::string start;

    bool expecting_lhs = true;
    std::string current_lhs;
    std::vector<std::string> current_alternative;

    uint i = 0;
    while (i < wss.size()) {
        if (expecting_lhs) {
            current_lhs = wss[i];
            nonTerminals.insert(current_lhs);
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
            if (nonTerminals.find(item2) == nonTerminals.end()) terminals.insert(item2);
        }
        std::cout << std::endl;
        y++;
    }
    start = find_start_symbol(rules);
    std::cout << "Start Symbol: " << start << '\n';
    std::cout << "Non-Terminals: " << nonTerminals.size();
    for (const std::string &r : nonTerminals){
        std::cout << ' ' << r;
    }
    std::cout << "\nTerminals: " << terminals.size();
    for (const std::string &r : terminals){
        std::cout << ' ' << r;
    }
    std::cout << '\n';
    std::cout << "\nnullable_set: ";
    nullableSet = compute_nullable_set(rules,nonTerminals);
    for (const std::string &r : nullableSet){
        std::cout << ' ' << r;
    }
    std::cout << '\n';
    std::cout << "\nFirstSet: ";
    std::set<std::string> seenSet;
    for (const std::string &r : GetFirstSet(std::vector<std::string>({"sTar"}),terminals,rules,nullableSet,seenSet)){
        std::cout << ' ' << r;
    }
    std::cout << '\n';
    std::cout << "\nFollowSet: ";
    seenSet.clear();
    for (const std::string &r : GetFollowSet("eNd",terminals,rules,nullableSet,seenSet)){
        std::cout << ' ' << r;
    }
    std::cout << '\n';


    return 0;
}