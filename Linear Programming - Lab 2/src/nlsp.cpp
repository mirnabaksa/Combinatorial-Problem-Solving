#include <ilcplex/ilocplex.h>
#include <vector>

using namespace std;
ILOSTLBEGIN

typedef vector<bool> VI;

class NLSP {
	private:
		IloEnv env;
		IloModel model;
		IloIntVarArray  node_codes;
		IloBoolVarArray  node_outputs;
		IloBoolVarArray is_NOR;
		IloBoolVarArray output_indicators;

		
		int n;
		int length;
		int num_types;
		int depth;
		int M1, M2, M3, M4;
		int* node_types;
		VI truth_table;

		// For storing the solution after solving the problem
		int* solution;
		int size;

	public:
		NLSP(int num_vars, int max_dep, const VI& table) :
			n(num_vars),
			num_types(n + 2),
			length(pow(2, max_dep) - 1),
			depth(max_dep),
			model(env),
			node_codes(env),
			node_outputs(env),
			is_NOR(env),
			output_indicators(env),
			truth_table(table)
			 {

			M1 = -1;
			M2 = n+1;
			M3 = 1;
			M4 = n;

			// [-1, 0, 1, ... n]
			node_types = new int[n + 2];
			for (int i = -1; i <= n; i++) node_types[i+1] = i;

			define_model();
		}

	void define_model() {
		// Node codes are in [-1, n] -> 0 represents NULL
		for (int i = 0; i < length; i++) {
			node_codes.add(IloIntVar(env, -1, n));
			is_NOR.add(IloBoolVar(env));
		}
		
		for (int i = 0; i < length; i++) {
			int left = 2 * i + 1;
			int right = 2 * i + 2;

			// is_NOR[i] has to be 1 if the node_codes[i] is -1
			//model.add(node_codes[i] + is_NOR[i] != -1);
			

			if (left < length) {
				model.add(node_codes[i] >= -1 - M1 * (1 - is_NOR[i]));
				model.add(node_codes[i] <= -1 + M2 * (1 - is_NOR[i]));

				model.add(node_codes[left] >= - M3 * is_NOR[i]);
				model.add(node_codes[left] <= M4 * is_NOR[i]);
			}
			else {
				// A NOR gate can not be a leaf
				model.add(node_codes[i] != -1);
				model.add(is_NOR[i] == 0);
			}


			if (right < length) {
				model.add(node_codes[i] >= -1 - M1 * (1 - is_NOR[i]));
				model.add(node_codes[i] <= -1 + M2 * (1 - is_NOR[i]));

				model.add(node_codes[right] >= 0 - M3 * is_NOR[i]);
				model.add(node_codes[right] <= 0 + M4 * is_NOR[i]);

			} else {
				// A NOR gate can not be a leaf
				model.add(node_codes[i] != -1);
				model.add(is_NOR[i] == 0);
			}
		}
		
		// Init node_outputs
		for (int i = 0; i < length * truth_table.size(); i++) {
			node_outputs.add(IloBoolVar(env, 0, 1));		
		}

		// Init indicators
		for (int i = 0; i < length; i++) {
			IloExpr expr(env);

			output_indicators.add(is_NOR[i]);
			expr += is_NOR[i];

			for (int k = 1; k < num_types; k++) {
				IloBoolVar x(env);
				output_indicators.add(x);
				expr += x;
			}

			// Only one indicator is active at a time
			model.add(expr == 1);
		}

		
		// Truth table assignments
		for (int i = 0, m = truth_table.size(); i < m; i++) {
			// First element of output array is equal to the truth table assignement
			model.add(output_at(i, 0) == truth_table[i]);

			// i-th row of truth table in binary 
			// e.g. for 3 vars the 0-th row is 000
			bool* table_row = get_table_row(i);

			bool* fixed_outputs = new bool[n + 1];
	
			fixed_outputs[0] = 0;
			for (int j = 1; j < n+1; j++) {
				fixed_outputs[j] = table_row[j-1];
			}

			// For every parent
			for (int j = 0; j < length; j++) {
				int left = 2 * j + 1;
				int right = 2 * j + 2;

				IloBoolVar NOR_output(env);
				if (left < length && right < length) {
					IloBoolVar x1 = output_at(i, left);
					IloBoolVar x2 = output_at(i, right);
					IloBoolVar or(env);
					model.add(or <= x1 + x2);
					model.add(or >= x1);
					model.add(or >= x2);
					IloBoolVar nor(env);
					model.add(nor == 1 - or );

					model.add(output_at(i,j) >= nor - 1*(1-is_NOR[j]));
					model.add(output_at(i,j) <= nor + 1*(1-is_NOR[j]));
				}


				IloExpr expr_code(env);
				IloExpr expr_out(env);
				for (int k = 0; k < num_types; k++) {
					expr_code += node_types[k] * output_indicators[j*num_types + k];
					if(k>0) expr_out += fixed_outputs[k-1] * output_indicators[j*num_types + k];
				}

				IloExpr expr_out_left(env);
				IloExpr expr_out_right(env);
				expr_out_left = expr_out + 0 * is_NOR[j];
				expr_out_right = expr_out + 1 * is_NOR[j];

				model.add(node_codes[j] >= expr_code);
				model.add(node_codes[j] <= expr_code);

				model.add(output_at(i, j) >= expr_out_left);
				model.add(output_at(i, j) <= expr_out_right);
			}

		}
	

		IloExpr minimize_size(env);
		for (int i = 0; i < length; i++) minimize_size += is_NOR[i];
		model.add(IloMinimize(env, minimize_size));
	}


	bool solve() {
		bool solution_found = false;
		IloCplex cplex(model);
		cplex.setOut(env.getNullStream());

		if (solution_found = cplex.solve()) {
			// Save solution size and node codes 
			IloNumArray sol(env);
			solution = new int[length];
			cplex.getValues(sol, node_codes);

			size = 0;
			IloNumArray nor(env);
			cplex.getValues(nor, is_NOR);
			for (int i = 0; i < length; i++) {
				size += nor[i];
				solution[i] = sol[i];
			}
		}
		env.end();
		return solution_found;
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


	IloBoolVar output_at(int i, int j) {
		return node_outputs[i*length + j];
	}

	void print_to_stream(ostream& out) {
		out << n << "\n";
		for (int i = 0, n = truth_table.size(); i < n; i++) out << truth_table[i] << "\n";
		out << depth - 1 << " " << size << "\n";

		print_tree(0, out);
	}

	void print_tree(int root, ostream& out) {
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
			print_tree(left-1, out);
			print_tree(right-1, out);
		}
	}

};

int main () {
	cerr << "Starting execution!" << "\n";

	int n;
	cin >> n;

	int m = pow(2, n);

	vector<bool> table;
	for (int i = 0; i < m; i++) {
		int x;
		cin >> x;
		table.push_back(x == 0 ? 0 : 1);
	}


	// Start with depth 1 and increase until the solution is found
	int depth = 1;

	while (1) {
		cerr << "Depth: " << depth << "\n";
		int length = pow(2, depth) - 1;
	
		NLSP* solver = new NLSP(n, depth, table);
		if (solver->solve()) { 
			cerr << "Solution found" << "\n";
			solver->print_to_stream(cerr);
			solver->print_to_stream(cout);
			break;
		}
		
		cerr << "Increasing depth" << "\n";
		depth++;
	}
	
}
