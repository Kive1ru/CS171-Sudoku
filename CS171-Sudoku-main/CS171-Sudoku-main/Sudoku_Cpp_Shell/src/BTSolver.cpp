#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
    map<Variable*, Domain> remap;
    for (Variable* variable : network.getVariables()) {
        if (variable->isModified() && variable->isAssigned()) {
            if (variable->getDomain().isEmpty() ) {
                return make_pair(remap, false);
            }
            for (Variable* neighbor : network.getNeighborsOfVariable(variable)) {
                if (neighbor->getDomain().contains(variable->getAssignment())) {
                    if (neighbor->isAssigned()){
                        return make_pair(remap, false);
                    }
                    if (neighbor->getDomain().size() == 1) {
                        return make_pair(remap, false);
                    }
                    if (neighbor->getDomain().size() == 0) {
                        return make_pair(remap, false);
                    }
                    trail->push(neighbor);
                    neighbor->removeValueFromDomain(variable->getAssignment());
                    remap.insert(pair<Variable*, Domain>(neighbor, neighbor->getDomain()));
                }
            }
        }
    }
    network.getModifiedConstraints();
    return make_pair(remap, network.isConsistent());
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    map<Variable*, int> remap;
    pair<map<Variable*,Domain>, bool> result = forwardChecking();
    if (result.second == false){
        return make_pair(remap, false);
    }
    for (Constraint constraint: network.getConstraints()){
        map<int, vector<Variable*>> counter;
        for (int value = 1; value <= constraint.size(); value++){
            counter[value] = {};
        }
        for (Variable* variable: constraint.vars){
            if (!variable->isAssigned() && variable->size() == 1){
                trail->push(variable);
                variable->assignValue(variable->getValues()[0]);
            }
            for (int value = 1; value <= constraint.size(); value++){
                if(variable->getDomain().contains(value)){
                    counter[value].push_back(variable);
                }
            }
        }

        for (pair<int, vector<Variable*>> pairs: counter){
            if (pairs.second.size() == 0){
                return make_pair(remap, false);
            }
            if (pairs.second.size() == 1){
                if (!pairs.second[0]->isAssigned()){
                    trail->push(pairs.second[0]);
                    pairs.second[0]->assignValue(pairs.first);
                    pair<map<Variable*,Domain>, bool> result = forwardChecking();
                    if (result.second == false){
                        return make_pair(remap, false);
                    }
                    remap.insert(pair<Variable*, int>(pairs.second[0], pairs.first));
                }
            }
        }
        if(!constraint.isConsistent()){
            return make_pair(remap, false);
        }
    }
    return make_pair(remap, assignmentsCheck());
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return norvigCheck().second;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
    int domainSize = 999999;
    Variable* returnVar = nullptr;
    ConstraintNetwork::VariableSet unassigned;
    for (Variable* variable : network.getVariables()) {
        if (!(variable->isAssigned())) {
            if (variable->size() < domainSize) {
                domainSize = variable->size();
                returnVar = variable;
            }
        }
    }
    return returnVar;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    vector<Variable*> tempvector;
    vector<Variable*> returnvector;
    map<Variable*, int> variablemap;
    ConstraintNetwork::VariableSet unassigned;
    for (Variable* variable : network.getVariables()) {
        if (!(variable->isAssigned())) {
            for (Variable* neighbor : network.getNeighborsOfVariable(variable)) {
                if (!neighbor->isAssigned()) {
                     variablemap[variable] += 1;
                }
            }
        }
    }
    if (variablemap.size() == 0) {
        returnvector.push_back(getfirstUnassignedVariable());
        return returnvector;
    }

    int counter = -1;
    int domainsize = 9999;
    for (pair<Variable*, int> variablepair : variablemap) {
        if (variablepair.first->getDomain().size() < domainsize) {
            tempvector.clear();
            domainsize = variablepair.first->getDomain().size();
            tempvector.push_back(variablepair.first);
        }
        else if (variablepair.first->getDomain().size() == domainsize) {
            tempvector.push_back(variablepair.first);
        }
    }
    for (Variable* variable : tempvector) {
        if (variablemap[variable] > counter) {
            returnvector.clear();
            counter = variablemap[variable];
            returnvector.push_back(variable);
        }
        else if (variablemap[variable] == counter) {
            returnvector.push_back(variable);
        }
    }
    return returnvector;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return MRVwithTieBreaker()[0];
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    map<int, int> LCVmap;
    vector<int> CVlist;
    vector<pair<int, int>> LCVvector;
    for ( int value : v->getValues()){
        LCVmap.insert(pair<int, int>(value, 0));
    }
    for(Variable* neighbor : network.getNeighborsOfVariable(v)){
        for ( int value : neighbor->getValues()){
            if (LCVmap.count(value) > 0){
                LCVmap[value] += 1;
            }
        }
    }
    for (pair<int, int> element: LCVmap)
        LCVvector.push_back(element);
    sort(LCVvector.begin(), LCVvector.end(), [](pair<int, int> const& a, pair<int, int> const& b){
        return a.second < b.second;});
    for (pair<int, int> element : LCVvector){
        CVlist.push_back(element.first);
    }
    return CVlist;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return getValuesLCVOrder(v);
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
