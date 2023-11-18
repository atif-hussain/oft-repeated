#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <functional>
#include <map>
using namespace std;
typedef unsigned short int _uint16;

struct Node {
    std::wstring sub = L"";   // a substring of the input string
    std::vector<size_t> ch;    // vector of child nodes
    Node() { } // empty
    Node(const std::wstring& sub, std::initializer_list<size_t> children) : sub(sub) {
        ch.insert(ch.end(), children);
    }
};

struct SuffixTree {
    std::vector<Node> nodes;
    SuffixTree(const std::wstring& str) {
        nodes.push_back(Node{});
        for (size_t i = 0; i < str.length(); i++) {
            addSuffix(str.substr(i));
        }
    }
    void visualize() {
        if (nodes.size() == 0) {
            std::cout << "\n";
            return;
        }

        std::function<void(size_t, const std::wstring&)> f;
        f = [&](size_t n, const std::wstring& pre) {
            auto children = nodes[n].ch;
            if (children.size() == 0) { std::wcout << "- " << nodes[n].sub << L".\n"; return;
            }
            std::wcout << "+ " << nodes[n].sub << L":\n";

            for (auto it = std::begin(children); (it) != std::end(children); it = std::next(it)) {
                std::wcout << pre << L"+-";
                f(*it, pre + ((next(it) != end(children)) ? L"| " : L"? "));
            }
        };

        f(0, L"");
    }
private:
    void addSuffix(const std::wstring& suf) {
        size_t n = 0;
        size_t i = 0;
        while (i < suf.length()) {
            wchar_t b = suf[i];
            int x2 = 0;
            size_t n2;
            while (true) {
                auto children = nodes[n].ch;
                if (x2 == children.size()) {
                    // no matching child, remainder of suf becomes new node
                    n2 = nodes.size();
                    nodes.push_back(Node(suf.substr(i), {}));
                    nodes[n].ch.push_back(n2);
                    return;
                }
                n2 = children[x2];
                if (nodes[n2].sub[0] == b) {
                    break;
                }
                x2++;
            }
            // find prefix of remaining suffix in common with child
            auto sub2 = nodes[n2].sub;
            size_t j = 0;
            while (j < sub2.size()) {
                if (suf[i + j] != sub2[j]) {
                    // split n2
                    auto n3 = n2;
                    // new node for the part in common
                    n2 = nodes.size();
                    nodes.push_back(Node(sub2.substr(0, j), { n3 }));
                    nodes[n3].sub = sub2.substr(j); // old node loses the part in common
                    nodes[n].ch[x2] = n2;
                    break; // continue down the tree
                }
                j++;
            }
            i += j; // advance past part in common
            n = n2; // continue down the tree
        }
    }
};

 
wofstream fout;
const int from = 0x621; const int sz = 0x34;//consonants 0x621-0x64A [ؠ-ي] + vowels [ڀً-ڀْ]
typedef wstring::iterator ptr;
const int N = 1000000, INF = 1000000000; wstring str;
unsigned int txn[N][sz]; //array of transitions; Corresponding: suffix-node <-> incoming edge <-> substring
ptr l[N], r[N]; // left,right boundaries of substring corresponding to incoming edge
unsigned int p[N], s[N]; // parent node, suffix link
unsigned int ts, tv; ptr tp, la; //#nodes; current suffix-node, str-pos, str-char

void ukk_add(int c) { // add character s to suffix-tree
    suff:;  // we'll return here after each transition to the suffix (and will add character again)
    if (tp >= r[tv]) { // check whether we're still within the boundaries of the current edge
        // if we're not, find the next edge. If it doesn't exist, create a leaf and add it to the tree
        if (txn[tv][c] == -1) { txn[tv][c] = ts; l[ts] = la; p[ts++] = tv; tv = s[tv]; tp = r[tv]; goto suff; }
        tv = txn[tv][c]; tp = l[tv];
    } // otherwise just proceed to the next edge
    if ((tp == str.begin() + 5 - 1) || c == *tp - from)
        tp++; // if the letter on the edge equal c, go down that edge
    else {
        // otherwise split the edge in two with middle in node ts
        l[ts] = l[tv];  r[ts] = tp;  p[ts] = p[tv]; txn[ts][*tp - from] = tv; 
        // add leaf ts+1. It corresponds to transition through c.
        l[ts + 1] = la; p[ts + 1] = ts; txn[ts][c] = ts + 1; 
        // update info for the current node - remember to mark ts as parent of tv
        l[tv] = tp;  p[tv] = ts;  txn[p[ts]][*(l[ts]) - from] = ts;  
        // prepare for descent
        // tp will mark where are we in the current suffix
        tv = s[p[ts]]; tp = l[ts];
        // while the current suffix is not over, descend
        while (tp<r[ts]) { tv=txn[tv][*tp-from]; tp+= r[tv]-l[tv];}
        // if we're in a node, add a suffix link to it, otherwise add the link to ts
        // (we'll create ts on next iteration).
        s[ts] = (tp == r[ts]) ? tv: (ts+2);
        // add tp to the new edge and return to add letter to suffix
        tp = r[tv] - (tp - r[ts]); ts += 2; goto suff;
    }
}
void build_SuffixTree() {
    // initialize suffix tree
    s[0] = 1; memset(txn, -1, sizeof txn); fill(txn[1], txn[1] + sz, 0);
	ts = 2; tv = 0; fill(r, r + N, str.end());  // tree root
    r[0] = str.begin()+5; r[1] = r[0]; tp = r[0]; l[0] = r[0]-1; l[1] = l[0];

    // add the text to the tree, letter by letter
    for (la = r[0]; la < str.end(); ++la)
        ukk_add(*la - from);
}
_uint16 rep[N]; // substring repeats count
struct freq { _uint16 rep; _uint16 wt; ptr from, to; };  vector<freq > oft;
void postProcess(void) {
    // Depth-First-Search on the Tree, to find substring' repeats ...
    if (ts == 0) { fout << L'\n'; return; }
    _uint16 pl = -1; bool logSfxT; bool push;
    std::function<void(int, const std::wstring&)> dfs;
    dfs = [&](const int t, const std::wstring& pre) {
        pl += (_uint16) (r[t] - l[t]);
        if (t < 0 || r[t] < l[t])
            cout << "ooch" << endl;
        if (logSfxT) fout << L"- "  << (t > 1 ? wstring(l[t], r[t]) : L"")
                 << L" ..." << rep[t] << L"x " << pl << L'\n';
        
        char i; rep[t] = 0;
        for (i = 0; i < sz; i++)
          if (txn[t][i] != -1) {
            if (logSfxT) fout << pre << L"+-";
            dfs(txn[t][i], pre + L"| ");
            rep[t] += rep[txn[t][i]];
        }
        if (rep[t] == 0) rep[t] = 1; //count child nodes only 
        if (push) { freq tmp = { rep[t], pl, r[t] - pl, r[t] }; oft.push_back(tmp); }
        pl -= (_uint16) (r[t] - l[t]);
    };
    oft.reserve(ts);
    fout << L'\n'; logSfxT = false; push=true; dfs(0, L""); //pass thru to compute repeats
    //fout << L'\n'; logSfxT = true; dfs(0, L""); //print substring repeats
    logSfxT = true; std::replace(str.begin(), str.end(), (wchar_t)0x63f, L' ');

    // Remove duplicates: after sorting by rep, to, wt(~= to-from)
    std::function<bool(const freq& a, const freq& b)> cmp;
    cmp = [&](const freq& a, const freq& b)->bool {
        if (a.rep != b.rep) return (a.rep < b.rep);
        if (a.to != b.to) return (a.to < b.to);
        return (a.wt < b.wt); };
    std::sort(oft.begin(), oft.end(), cmp);
    for (vector<freq>::iterator i = oft.begin(); i < oft.end() - 1; i++)
        if ((*i).rep==(*(i+1)).rep and (*i).to == (*(i + 1)).to) (*i).rep = 0;

    for (vector<freq>::iterator i = oft.begin(); i < oft.end() - 1; i++) {
        if (((*i).wt > 2) && (*((*i).from) != L' ' || *((*i).to - 1) != L' ')) //if not start or not end in ' '
            //for (auto x = (*i).from + 1; x < (*i).to - 1; x++) if (*x == L' ') (*i).rep = 0; ...Inefficient, so commented.
            if ((*i).wt > 5) (*i).rep = 0;
    }
        
    // all done; now print substrings, by their repeats DESC, wt DESC
    cmp = [&](const freq& a, const freq& b)->bool {
        int r = a.rep*a.rep*a.wt - b.rep*b.rep*b.wt; if (r) return (r > 0);
        if (a.rep != b.rep) return (a.rep > b.rep);
        return (a.wt > b.wt);
    };
    std::sort(oft.begin(), oft.end(), cmp);
    for (auto& a : oft) if (logSfxT && a.rep > 1)
        fout << a.rep << L"x\t" << (a.to-a.from) << L"ch:\t" << wstring(a.from, a.to) << L'\n';
}
int main(int argc, char* a[])
{
    wifstream fin("sampleInputs/_quran-simple.txt"); fin.imbue(std::locale("zh_CN.UTF-8"));
    fout.open("sampleOutputs/output.txt"); fout.imbue(std::locale("zh_CN.UTF-8"));
    wstring text; size_t len = 0; str = L"12345";
    wchar_t c; map<wchar_t, int> histogram;
    while (!fin.eof()) {
        fin.get(c); histogram[c]++;
        if (c == L'#') break; // * stop Reading at 1st '#', in these input files
        if (c == L' ' || c == L'\n') { c = (wchar_t)0x63f; //unused char in range
            if (*(str.end() - 1) == c) continue; } //don't double-add iff continous
        if (c == 0x670 || c == 0x671) c = 0x627; //superscript Alef or Alef wasla
        if (c >= from && c < from + sz) { str.push_back(c); len++; }
        //else std::cout << "ignore char, don't push " << hex << (int)c << " at " << len << '\n';
    }   fin.close();

    //for (auto& e : histogram) { fout << hex << L"0x" << (int)e.first << L" " << e.first << L'\t' << dec << e.second << endl; }
    std::cout << "read " << len << " chars" << endl << endl;

    // testing on various inputs, and of implmentations
    //str = L"bananay";
    //str = L"i wish to wish the wish you wish to wish but if you wish the wish the witch wishes i wont wish the wish you wish to wish";
    // SuffixTree(str).visualize();

    build_SuffixTree();
    postProcess();

    fout.close();
    return 0;
}
