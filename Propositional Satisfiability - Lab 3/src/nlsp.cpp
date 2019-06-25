#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <assert.h>
#include <stdlib.h>
#include <cmath>

#define command "tac tmp.rev | lingeling | grep -E -v \"^c\"  | cut --delimiter=' ' --field=1 --complement > tmp.out"
#define V +

using namespace std;


int n;
int n_vars;
int n_clauses;
int n_literals;

ofstream cnf;
ifstream sol;
fstream tmp;

typedef string literal;
typedef string clause;
typedef vector<bool> VI;

int length;
int num_types;
int depth;
int size;

string* node_types;
string* node_outputs;
VI truth_table;

literal operator-(const literal& lit) {
  if (lit[0] == '-') return lit.substr(1); 
  else               return "-" + lit;
}


literal node_type(int i, int j) {
  return node_types[i*num_types+j] + " ";
}

literal node_output(int i, int j) {
  return node_outputs[i*length+j] + " ";
}

void add_clause(const clause& c) {
  cnf << c << "0" << endl;
  ++n_clauses;
}


void add_at_most_one(const vector<literal>& z) {
  int N = z.size();
  for (int i1 = 0; i1 < N; ++i1)
    for (int i2 = i1+1; i2 < N; ++i2)
      add_clause(-z[i1] V -z[i2]);
}

void add_at_least_one(const vector<literal>& z) {
  clause c;
  for(int i = 0; i < z.size(); i++) {
    c = c V z[i];
  }
  add_clause(c);
}


bool* get_table_row(int i) {
		bool* table_row = new bool[n]();
		int k = n - 1;

		do {
			table_row[k--] = i & 1;
			i /= 2;
		} while (i > 0);

		return table_row;
	}



void write_CNF() {
  n_vars = 0;
  n_clauses = 0;

  node_types = new string[length*num_types];

  for(int i = 0; i < length; i++)
    for(int j = 0;  j < num_types; j++) 
      node_types[i*num_types+j] = to_string(i*num_types+j+1);
  
  // Node relationship
  n_vars += length * num_types;
  for(int i = 0; i < length; i++) {
    int left = 2 * i + 1;
    int right = 2 * i + 2;

   vector<literal>  all;
    for(int type = -1; type <= n; type++){
      all.push_back(node_type(i, type+1));
    }
    add_at_most_one(all);
    add_at_least_one(all);
    
    // Forbid NOR
    if( left >= length || right >= length) {
      add_clause(-node_type(i,0));
      continue;
    }

    clause nor_left = -node_type(i,0);
    clause nor_right = -node_type(i,0);

    for(int type = -1; type <= n; type++) {
      nor_left = nor_left V node_type(left,type+1);
      nor_right = nor_right V node_type(left,type+1);
    }
    
    add_clause(nor_left);
    add_clause(nor_right);

    for(int type = 0; type <= n; type++){
      add_clause(-node_type(i,type+1) V node_type(left,1));
      add_clause(-node_type(i,type+1) V node_type(right,1));
    }
  }

  node_outputs = new string[truth_table.size()*length];
  for(int i = 0; i < truth_table.size() * length; i++) {
    node_outputs[i] = to_string(n_vars+1+i);
  }

  n_vars += truth_table.size() * length;
   // Truth table assignments
		for (int i = 0, m = truth_table.size(); i < m; i++) {
			// First element of output array is equal to the truth table assignement
      clause c;
      if(truth_table[i]) c = node_output(i, 0);
      else c = -node_output(i, 0);
      add_clause(c);


      // i-th row of truth table in binary 
			// e.g. for 3 vars the 0-th row is 000
			bool* table_row = get_table_row(i);

      for(int j = 0; j < length; j++){
        for(int type = -1; type <= n; type++){

            if(type == -1){
              int left = 2 * j + 1;
				      int right = 2 * j + 2;

              if (left < length && right < length) {
                //a -> (!(b+c) eq d)
                add_clause(-node_type(j, type+1) V -node_output(i, left) V -node_output(i,j));
                add_clause(-node_type(j, type+1) V node_output(i,left) V node_output(i, right) V node_output(i,j));
                add_clause(-node_type(j, type+1) V -node_output(i, right) V -node_output(i,j));
              }

            }else if(type == 0){
              add_clause(-node_type(j,type+1) V -node_output(i,j));
            } else if(type > 0){
                bool val = table_row[type-1];
                if(val) add_clause(-node_type(j,type+1) V node_output(i,j));
                else add_clause(-node_type(j,type+1) V -node_output(i,j));

            }

        }


      }

    }

}


literal create_literal() {
	n_vars++;
	return to_string(n_vars) + " ";
}


vector<literal> two_comp(literal x1, literal x2) {
	literal y1 = create_literal();
	literal y2 = create_literal();

	// x1 -> y1
	add_clause(-x1 V y1);
	// x2 -> y1
	add_clause(-x2 V y1);
	// x1 and x2 -> y2
	add_clause(-x1 V -x2 V y2);

	vector<literal> result;
	result.push_back(y1);
	result.push_back(y2);
	return result;
}


vector<literal> merge(vector<literal> x1, vector<literal> x2) {
	if (x1.size() != x2.size()) {
		throw exception();
	}

	int n = x1.size();
	if (n == 1) return two_comp(x1[0], x2[0]);

	vector<literal> x1_odd, x1_even, x2_odd, x2_even;
	for (int i = 0; i < n; i++) {
		if (i % 2 == 0) {
			x1_odd.push_back(x1[i]);
			x2_odd.push_back(x2[i]);
		}
		else {
			x1_even.push_back(x1[i]);
			x2_even.push_back(x2[i]);
		}
	}

	vector<literal> z_odd = merge(x1_odd, x2_odd);
	vector<literal> z_even = merge(x1_even, x2_even);

	vector<literal> result;
	result.push_back(z_odd[0]);
	
	int j = 1;
	for (int i = 1; i < n; i++) {
		vector<literal> tmp = two_comp(z_odd[i], z_even[i - 1]);
		result.push_back(tmp[0]);
		result.push_back(tmp[1]);
	}

	result.push_back(z_even[n - 1]);
	return result;
}

vector<literal> sorting(vector<literal> x) {
    int n = x.size();
    if( n == 2 ) return two_comp(x[0], x[1]);

    vector<literal> beginning = sorting(std::vector<literal>(x.begin(), x.begin() + n/2));
    vector<literal> end = sorting(std::vector<literal>(x.begin() + n/2, x.end()));

    return merge(beginning, end);
}

vector<literal> start_sorting(vector<literal> x) {
   	// pad length to power of n
    int m = ceil(log2(x.size())); 
    int padded_size = pow(2,m);
    for(int i = x.size(); i < padded_size; i++) {
        literal pad = create_literal();
        x.push_back(pad);
        add_clause(-pad);
    }
    
    return sorting(x);
}

void write_size_constraints() {
  int k = size;
  vector<literal> node_types;
  for(int i = 0; i < length; i++) node_types.push_back(node_type(i, 0));

  vector<literal> results = start_sorting(node_types);

  add_clause(-results[size]);

}

void write_heading() {
   cnf << "p cnf " << n_vars << " " << n_clauses << endl;
}


void print_tree(int root, int* solution, ostream& out) {
		int id = root + 1;
		int code = solution[root];
    
		int left = 0;
		int right = 0;
		if (code == -1) {
			left = (2 * root + 1) + 1;
			right = (2 * root + 2) + 1;
		}

		out << id << " " << code << " " << left << " " << right << "\n";
		
		if (code == -1) {
			print_tree(left-1, solution, out);
			print_tree(right-1, solution, out);
		}
	}


void print_to_stream(ostream& out, int* solution) {
		out << n << "\n";
		for (int i = 0, n = truth_table.size(); i < n; i++) out << truth_table[i] << "\n";

		out << depth - 1 << " " << size << "\n";

		print_tree(0, solution, out);
	}


bool get_solution() {
  sol.open("tmp.out");

  string solution;
  sol >> solution;
  if (solution == "UNSATISFIABLE") {
    sol.close();
    return false;
  }

  size = 0;
  int* result = new int[length];
  int j = 0;
  int* node_types = new int[length*num_types];
  for(int i = 0; i < length * num_types; i++) {
    int type;
    sol >> type;
    if(type > 0) {
      result[j] = i%num_types-1;
      if(result[j++] == -1) size++;
    }
    node_types[i] = type > 0? 1 : 0;
  }

  tmp.open("tmp_output.out",  std::ofstream::out | std::ofstream::trunc);
  print_to_stream(tmp, result);
  tmp.close();

  sol.close();
  return true;
}


int main(int argc, char** argv) {
  cerr << "Starting execution!" << "\n";

  cin >> n;
	int m = pow(2, n);
  num_types = n+2;

  // Truth table
	for (int i = 0; i < m; i++) {
		int x;
		cin >> x;
		truth_table.push_back(x == 0 ? 0 : 1);
	}

	// Start with depth 1 and increase until the solution is found
	depth = 1;

	while (1) {
		cerr << "Depth: " << depth << "\n";
		length = pow(2, depth) - 1;
    size = length;
	
    cnf.open("tmp.rev");
    write_CNF();
    write_heading();
    cnf.close();

    system(command);

    if(get_solution()) {
      cerr << "Found solution, minimizing size... " << size << "\n";
      // Minimizing the size
      //size--;
   while(size > 0) {

        cnf.open("tmp.rev");
        write_CNF();
        write_size_constraints();
        write_heading();
        cnf.close();

        system(command);
        
        if(!get_solution()) {
            break;
        } 
        
        size --;
      }


       break;
    }
    
		cerr << "Increasing depth" << "\n";
		depth++;
	}

  string line;
  ifstream output ("tmp_output.out");
  if (output.is_open())
  {
    while ( getline (output,line) )
    {
      cout << line << '\n';
    }
    output.close();
  }
}
