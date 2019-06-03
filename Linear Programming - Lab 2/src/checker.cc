#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <cstdlib>
#include <getopt.h>
#include <time.h> 

using namespace std;


struct Node {
  int code, lp, rp;
  Node(int code_arg = -2, int lp_arg = -2, int rp_arg = -2) :
    code(code_arg), lp(lp_arg), rp(rp_arg) { }
};


int d, n, ub_n_nodes, n_gates;
vector<Node> circ;
vector<int>  b;

string png_viewer;


bool eval_circuit(int id, const vector<bool>& s) {
  assert(1 <= id  and  id <= ub_n_nodes);
  int code  = circ.at(id).code;
  int left  = circ.at(id).lp;
  int right = circ.at(id).rp;
  if (code == -1) {
    return not(eval_circuit(left, s) or eval_circuit(right, s));
  }
  else {
    assert(left  == 0);
    assert(right == 0);
    if (code == 0) return 0;
    else {
      assert(1 <= code and code <= n);
      return s[code-1];
    }
  }
}


bool eval_circuit(const vector<bool>& s) {
  return eval_circuit(1, s);
}


bool gen_and_eval(int i, vector<bool>& s) {
  if (i == n) {
    bool xpct = b.back();
    b.pop_back();
    bool eval = eval_circuit(s);
    if (eval != xpct) {
      cout << "Error: evaluating the circuit at boolean assignment " << endl;
      for (int k = 0; k < n; ++k)
        cout << "x" << k+1 << " ";
      cout << endl;
      for (int k = 0; k < n; ++k)
        cout << s[k] << "  ";
      cout << endl;
      cout << "yields value " << eval << " but value " << xpct << " was expected" << endl;
      return false;
    }
  }
  else {
    s[i] = 0; if (not gen_and_eval(i+1, s)) return false;
    s[i] = 1; if (not gen_and_eval(i+1, s)) return false;
  }
  return true;
}


int size(int id) {
  if (circ.at(id).code != -1) return 0;
  else return 1 + size(circ.at(id).lp) + size(circ.at(id).rp);
}


int size() {
  return size(1);
}


int depth(int id) {
  if (circ.at(id).code != -1) return 0;
  else return 1 + max(depth(circ.at(id).lp), depth(circ.at(id).rp));
}


int depth() {
  return depth(1);
}


void check_circuit() {
  vector<bool> s(n);
  if (not gen_and_eval(0, s))
    exit(EXIT_FAILURE);

  int n_gates2 = size();
  if (n_gates2 != n_gates) {
    cout << "Error: circuit has size " << n_gates2 << " "
         << "but expected size " << n_gates << endl;
    exit(EXIT_FAILURE);
  }

  int d2 = depth();
  if (d2 != d) {
    cout << "Error: circuit has size " << d2 << " "
         << "but expected size " << d << endl;
    exit(EXIT_FAILURE);
  }
  
  cout << "OK!" << endl;
}


void plot_circuit() {

  srand(time(NULL));
  int id = rand() % 1000;
  string dot_file = "pic/tmp-nlsp-" + to_string(id) + ".dot";
  string png_file = "pic/tmp-nlsp-" + to_string(id) + ".png";
  
  ofstream out(dot_file);
  out << "digraph G {" << endl;
  int ub = (1 << (d+1)) - 1;
  for (int id = 1; id < circ.size(); ++id) {
    int code  = circ[id].code;
    int left  = circ[id].lp;
    int right = circ[id].rp;
    if (code == -2) continue;
    
    if (code == -1) {
      assert(1 <= left  and  left <= ub);
      assert(1 <= right and right <= ub);
      out << id << "[shape=box, color=cyan, style=filled, label=\"NOR\"]" << endl;
      out << left  << " -> " << id << ";" << endl;
      out << right << " -> " << id << ";" << endl;
    }
    else if (code == 0) {
      assert(left  == 0);
      assert(right == 0);
      out << id << "[shape=triangle, color=red, style=filled, label=\"0\"]" << endl;
    }
    else {
      assert(1 <= code and code <= n);
      assert(left  == 0);
      assert(right == 0);
      out << id << "[shape=circle, label=\"x" << code << "\"]" << endl;
    }
  }
  out << "}" << endl;
  out.close();
  system(string("dot -Tpng " + dot_file + " > " + png_file).c_str());
  cout << "Stored plot in PNG format in file " << png_file << endl;
  cout << "Calling " + png_viewer + " to view PNG... " << endl;
  system(string(png_viewer + " " + png_file + " &").c_str());
}


void help(string exe) {
  cout << "Checks that a circuit of the Nor Logic Synthesis Problem satisfies its specification" << endl;
  cout << "Usage: " << exe << " [options] [< nlsp_n_b.out]" << endl;
  cout << "Available options:" << endl;
  cout << "--viewer=png-viewer  -v png-viewer   set PNG viewer (default: display)" << endl;
  cout << "--plot               -p              plot circuit"                      << endl;
  cout << "--help               -h              print help"                        << endl;   
}


int main(int argc, char** argv) {

  struct option long_options[] = {
    {"viewer",         required_argument,  0, 'v'},
    {"plot",           no_argument,        0, 'p'},
    {"help",           no_argument,        0, 'h'},
    {0, 0, 0, 0}
  };

  png_viewer = "display";
  bool plot = false;
  
  while (true) {
    int option_index = 0;
    int c = getopt_long(argc, argv, "v:ph", long_options, &option_index);
    if (c == -1) break;
    switch (c) {

    case 'v':
      png_viewer = optarg;
      break;

    case 'p':
      plot = true;
      break;

    // case 'h':
    default:
      help(argv[0]);
      exit(EXIT_SUCCESS);
    }
  }

  cin >> n;
  b = vector<int>(1 << n);
  for (int k = b.size()-1; k >= 0; --k)
    cin >> b[k];
  
  cin >> d >> n_gates;

  ub_n_nodes = (1 << (d+1)) - 1;
  circ = vector<Node>(ub_n_nodes + 1);

  // Read circuit.
  int id, code, left, right;
  while (cin >> id >> code >> left >> right) {
    circ.at(id).code = code;
    circ.at(id).lp   = left;
    circ.at(id).rp   = right;
  }

  // Check.
  check_circuit();

  if (plot) plot_circuit();
}
