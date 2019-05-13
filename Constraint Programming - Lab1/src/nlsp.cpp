#include <fstream>
#include <vector>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>
#include <gecode/search.hh>

using namespace std;
using namespace Gecode;

typedef vector<bool> VI;

class NLSP : public Space {

private:
  int n_signals;
  int length;
  int max_depth;
  VI truth_table;

protected:
  // Array representation of a binary tree 
  IntVarArray node_codes;
  BoolVarArray node_outputs;

public:
  NLSP(int num_vars, int max_dep, const VI& table) : 
			n_signals(num_vars), 
            length(pow(2, max_dep)-1),
            max_depth(max_dep), 
            node_codes(*this, length, -2, n_signals), 
            node_outputs(*this, length * truth_table.size(), 0, 1),
            truth_table(table) {

    // First node can not be NULL
    rel(*this, node_codes[0], IRT_NQ, -2);

    for(int i = 0; i < length; i++) {
        int left = 2*i+1;
        int right = 2*i+2;
        
        if(left < length) { 
            // If it is a NOR gate - children can not be NULL
            // If not a NOR gate - children have to be NULL
            rel(*this, node_codes[i] == -1 && node_codes[left] != -2 || node_codes[i] != -1 && node_codes[left] == -2);
        } else {
            // A NOR gate can not be a leaf
             rel(*this, node_codes[i] != -1);
        } 

        if(right < length) {
            // If it is a NOR gate - children can not be NULL
            // If not a NOR gate - children have to be NULL
            rel(*this, node_codes[i] == -1 && node_codes[right] != -2 || node_codes[i] != -1 && node_codes[right] == -2);
        } else{
            // A NOR gate can not be a leaf
            rel(*this, node_codes[i] != -1);
        }
    }

    // Truth table constraints
    for(int i = 0, m = truth_table.size(); i < m; i++) {

        // First el of output array is equal to the truth table assignement
        rel(*this, output_at(i, 0) == truth_table[i]);

        bool* table_row = get_table_row(i);

        for(int j = 0; j < length; j++){
            int left = 2*j+1;
            int right = 2*j+2;

            // NOR gates have NOR output
            if(left < length && right < length)
                rel(*this, node_codes[j] != -1 || output_at(i, j) == (!(output_at(i,left) || output_at(i,right))));
            
            // Zero signal gates have output 0
            rel(*this, node_codes[j] != 0 || output_at(i,j) == 0);


            // Xi signals
            for(int k = 0; k < n_signals ; k++){
                rel(*this, node_codes[j] != k+1 || output_at(i, j) == table_row[k]);
            }

            rel(*this, node_codes[j] != -2 || output_at(i, j) == NULL);
                
        }
    }

    branch(*this, node_codes, INT_VAR_SIZE_MIN(), INT_VAL_MIN());
    branch(*this, node_outputs, BOOL_VAR_NONE(), BOOL_VAL_MIN());
  }

  NLSP(NLSP& s) : Space(s) {
	n_signals = s.n_signals;
    length = s.length;
    max_depth = s.max_depth;
    truth_table = s.truth_table;
    node_codes.update(*this, s.node_codes);
    node_outputs.update(*this, s.node_outputs);
  }

  virtual Space* copy() {
    return new NLSP(*this);
  }


  virtual void constrain(const Space& _b) {
    const NLSP& b = static_cast<const NLSP&>(_b);

    int best_size = 0;
    for(int i = 0; i < length; i++) {
          if(b.node_codes[i].val() == -1) best_size++;
      }

    count(*this, node_codes, -1, IRT_LE, best_size);
  }

  void print_to_err(void) const {
    cerr << "Found: ";
    for(int i = 0, m = node_codes.size(); i < m; i++) cerr << node_codes[i].val() << " ";
    cerr << "\n";
    cerr << "Outputs: " << "\n";

   for(int i = 0, m = truth_table.size(); i < m; i++) {
        for(int j = 0; j < length; j++){
            if(node_codes[j].val() == -2) cerr << "- ";
            else cerr << node_outputs[i*length+j].val() << " ";
        } 
        cerr << "\n";
    }
    cerr << "\n";
  }

  void print_to_out() {
      cout << n_signals << "\n";
      for(int i = 0, n = truth_table.size(); i < n; i++) cout << truth_table[i] << "\n";
      cout << max_depth-1 << " " << size() << "\n";

      for(int i = 0; i < length; i++) {
          int id = i+1;
          int code = node_codes[i].val();
          if(code == -2) continue;

          int left = 0;
          int right = 0;
          if(code == -1) {
            left = (2*i+1) + 1;
            right = (2*i+2) + 1;
          }

        cout << id << " " << code << " " << left << " " << right << "\n";
      }

  }

  int size() {
      int size = 0;
      for(int i = 0; i < length; i++){
          if(node_codes[i].val() == -1) size++;
      }
      return size;
  }


  BoolVar output_at(int i, int j) {
      return node_outputs[i*length+j];
  }

  bool* get_table_row(int i){
        bool* table_row = new bool[n_signals]();
        int k = n_signals-1;

        do{
             table_row[k--] = i & 1;
             i /= 2;
        } while(i > 0);

        return table_row;
  }
};


int main(int argc, char* argv[]) {
	cerr << "Starting execution!" << "\n";
	
    int n;
    cin >> n;

    int m = pow(2,n);

    vector<bool> table;
    for(int i = 0; i < m; i++) {
        int x;
        cin >> x;
        table.push_back(x == 0? 0 : 1);
    }
    
    // Start with depth 1 and increase until the solution is found
    int depth = 1;

    while(1) {

        try {
            cerr << "Depth: " << depth << "\n";

            NLSP* mod = new NLSP(n, depth, table);
            BAB<NLSP> e(mod);
            delete mod;

            NLSP* sant = e.next();
            NLSP* s = e.next();
            
            if(sant == NULL) {
                cerr << "Increasing depth!" << "\n";
                depth ++;
                continue;
            } else{
                 while (s != NULL) {
                    delete sant; 
                    sant = s;
                    s = e.next();
                }
                sant->print_to_err();
                sant->print_to_out();
                delete sant;
                break;
            }

        } catch (Exception e) {
        cerr << "Gecode exception: " << e.what() << endl;
        return 1;
         }

    }
   
  return 0;
}