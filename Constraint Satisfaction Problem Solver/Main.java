/* Main.java
 * 
 * 		Compile with: 	'javac Main.java'
 * 		Run with: 		'java Main <var-file> <con-file> <consistency-enforcing-procedure>'
 * 
 *		Description:	A CSP solver that prints the first 30 branches visited or stops when a
 *							solution is found. Allows for no consistency-enforcing procedure to
 *							be used or for forward checking to be used.
 */

import java.io.*;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Scanner;

public class Main {

	static ArrayList<Character> vars;
	static ArrayList<String[]> cons;
	static int iteration, type;
	
	public static void main(String[] args) throws FileNotFoundException {
		
		// Make sure the correct number of arguments are provided
		if(args.length == 3)
		{
			String varFile = args[0];
			String conFile = args[1];
			String proc = args[2];
			
			// Get the variable names from the var file
			Scanner sc1 = new Scanner(new File(varFile));

			// Initialize an ArrayList for the variable names
			vars = new ArrayList<Character>();
			
			// Loop through lines in var file
			while(sc1.hasNextLine()) {
				String next = sc1.nextLine();
				if(!next.trim().isEmpty()) {
					vars.add(next.charAt(0));
				}
			}
			sc1.close();
			
			// Get lines from the var file
			Scanner sc2 = new Scanner(new File(varFile));
			
			// Initialize an ArrayList for the variable values
			ArrayList<ArrayList<Integer>> varDomains = new ArrayList<ArrayList<Integer>>(vars.size());
			
			// Loop through lines in var file
			for(int i = 0; sc2.hasNextLine(); i++) {
				String next = sc2.nextLine();
				if(!next.trim().isEmpty()) {
					String[] splitLine = next.split("\\s+");
					
					ArrayList<Integer> domain = new ArrayList<Integer>();
					for(int j = 1; j < splitLine.length; j++)
						domain.add(Integer.parseInt(splitLine[j]));
					
					varDomains.add(domain);
				}
			}
			sc2.close();

			// Get the constraints from the con file
			Scanner sc3 = new Scanner(new File(conFile));

			// Initialize an ArrayList for the constraints
			cons = new ArrayList<String[]>();
			
			// Loop through lines in con file
			while(sc3.hasNextLine()) {
				String next = sc3.nextLine();
				if(!next.trim().isEmpty()) {
					String[] splitLine = next.split("\\s+");
					int var1 = varIndex(splitLine[0].charAt(0));
					int var2 = varIndex(splitLine[2].charAt(0));
					String[] con = {""+var1, splitLine[1], ""+var2};
					cons.add(con);
				}
			}
			sc3.close();

			// Determine which consistency-enforcing procedure to use
			if(Objects.equals(proc, "fc"))
				type = 1;
			else if(Objects.equals(proc, "none"))
				type = 0;
			else {
				System.out.println(proc + " is not a valid consistency-enforcing procedure.");
				return;
			}

			// Run backtracking
			iteration = 1;
			backtracking(varDomains, new Integer[vars.size()], new ArrayList<Integer>());
		}
		
		// Output a message if the incorrect number of arguments is provided
		else
			System.out.println("Incorrect number of arguments. Execute with: 'java Main <var-file> <con-file> <consistency-enforcing-procedure>'");
	}
	
	/* Returns the index of a given variable name in the vars array
	 *		Input:	Variable name	(Character x)
	 *
	 *		Output:	Variable index	(int)
	 */
	public static int varIndex(Character x)
	{
		for(int i = 0; i < vars.size(); i++)
			if(vars.get(i) == x)
				return i;
		return -1;
	}
	
	/* Backtracks for 30 iterations or until a complete assignment is found for the given CSP and prints the branches traversed as it runs
	 *		Input:	The domain for all the variables								(ArrayList<ArrayList<Integer>> varDomains)
 	 *				The assignment for the variables at the current iteration		(Integer[] assignment)
	 *				The order that the variables were assigned in					(ArrayList<Integer> varOrder)
	 *
	 *		Output:	The solution (assignment) or null if a solution is not found	(Integer[])
	 */
	public static Integer[] backtracking(ArrayList<ArrayList<Integer>> varDomains, Integer[] assignment, ArrayList<Integer> varOrder)
	{
		// If over 30 branches have been visited, stop backtracking
		if(iteration > 30)
			return null;

		// If the assignment is complete, print and return it
		if(complete(assignment))
		{
			// Print the solution
			printIteration(assignment, varOrder);
			System.out.println("  solution");
			
			// Return the assignment
			return assignment;
		}
		
		// Choose the next variable to assign
		int var = nextVar(varDomains, assignment);
		
		// Keep track of the previous values that have been assigned to var
		ArrayList<Integer> prevVals = new ArrayList<Integer>();
		for(int i = 0; i < varDomains.get(var).size(); i++)
		{
			// Choose the next variable value
			int val = nextVal(var, prevVals, varDomains, assignment);
			prevVals.add(val);
			
			// Add var=val to the assignment
			Integer[] tempAssignment = new Integer[assignment.length];
			tempAssignment = assignment.clone();
			tempAssignment[var] = val;

			// Add the current var to the variable order
			ArrayList<Integer> tempVarOrder = new ArrayList<Integer>(varOrder);
			tempVarOrder.add(var);
			
			// If the assignment is consistent with the CSP
			if(consistent(tempAssignment))
			{
				Integer[] result;
				
				// If consistency-enforcing procedure is none, backtrack immediately
				if(type == 0)
					result = backtracking(varDomains, tempAssignment, tempVarOrder);
				
				// If consistency-enforcing procedure is fc
				else {
					// Used forward-checking and adjust the domains of the variables
					ArrayList<ArrayList<Integer>> newVD = adjustVarDomains(var, varDomains, tempAssignment);
					
					// If a variable has no values remaining in its domain, the assignment cannot be a solution (skip backtracking with var=val)
					boolean skip = false;
					for(int j = 0; j < vars.size(); j++)
						if(newVD.get(j).size() == 0) {
							skip = true;
							break;
						}
					
					// Print the failed branch
					if(skip){
						printIteration(tempAssignment, tempVarOrder);
						System.out.println("  failure");
						result = null;
					}
					
					// If all variables have at least one value that they can be, continue backtracking
					else	
						result = backtracking(newVD, tempAssignment, tempVarOrder);
				}
				
				// If assigning var=val led to a solution, return it
				if(result != null)
					return result;
			}
			
			// If the assignment is not consistent with the CSP, print the failed branch
			else
			{
				printIteration(tempAssignment, tempVarOrder);
				System.out.println("  failure");
			}
		}
		
		// Return null if no solution is found
		return null;
	}
	
	/* Prints the assignment (branch) with the correct ordering
	 *		Input:	The assignment for the variables at the current iteration	(Integer[] assignment)
	 *				The order that the variables were assigned in				(ArrayList<Integer> varOrder)
	 */
	public static void printIteration(Integer[] assignment, ArrayList<Integer> varOrder)
	{
		// Print the current iteration
		System.out.print(iteration + ". ");
		
		// Loop through the variable ordering and print each var=val pair
		for(int i = 0; i < varOrder.size(); i++) {
			if(assignment[varOrder.get(i)] != null) {
				System.out.print(vars.get(varOrder.get(i)) + "=" + assignment[varOrder.get(i)]);
				if(i < varOrder.size()-1)
					System.out.print(", ");
			}
		}
		
		// Increment the current iteration
		iteration++;
	}
	
	/* Determines if the provided assignment is complete (is a solution to the CSP), assuming that it is consistent already
	 *		Input:	The assignment for the variables at the current iteration	(Integer[] assignment)
	 *
	 *		Output:	True if the assignment is complete and false otherwise		(boolean)
	 */
	public static boolean complete(Integer[] assignment)
	{
		// Make sure no variables in the assignment have a null value
		for(int i = 0; i < assignment.length; i++)
			if(assignment[i] == null)
				return false;
		return true;
	}

	/* Determines if the provided assignment is consistent with the CSP
	 *		Input:	The assignment for the variables at the current iteration	(Integer[] assignment)
	 *
	 *		Output:	True if the assignment is consistent and false otherwise	(boolean)
	 */
	public static boolean consistent(Integer[] assignment)
	{
		// Loop through all constraints
		for(int i = 0; i < cons.size(); i++)
		{
			// Get the next constraint
			String[] con = cons.get(i);
			Integer varVal1 = assignment[Integer.parseInt(con[0])];
			Integer varVal2 = assignment[Integer.parseInt(con[2])];
			
			// Make sure both variables of the constraint are assigned in the assignment
			if(varVal1 != null && varVal2 != null)
			{
				// Make sure the constraints are satisfied
				if(Objects.equals(con[1], "=") && varVal1 != varVal2)
					return false;
				else if(Objects.equals(con[1], "!") && varVal1 == varVal2)
					return false;
				else if(Objects.equals(con[1], ">") && varVal1 <= varVal2)
					return false;
				else if(Objects.equals(con[1], "<") && varVal1 >= varVal2)
					return false;
			}
		}
		return true;
	}

	/* Chooses the next unassigned variable to be assigned
	 *		Input:	The domain for all the variables							(ArrayList<ArrayList<Integer>> varDomains)
 	 *				The assignment for the variables at the current iteration	(Integer[] assignment)
	 *
	 *		Output:	The index of the variable chosen (in vars)					(int)
	 */
	public static int nextVar(ArrayList<ArrayList<Integer>> varDomains, Integer[] assignment)
	{
		int bestVar = -1;
		
		// Loop through the variables
		for(int i = 0; i < vars.size(); i++)
		{
			// If the variable is unassigned
			if(assignment[i] == null)
			{
				// Use most constrained variable heuristic
				if(bestVar == -1 || varDomains.get(i).size() < varDomains.get(bestVar).size())
					bestVar = i;
				
				// Deal with ties
				else if(varDomains.get(i).size() == varDomains.get(bestVar).size())
				{
					int iNum = countConstraints(i, assignment);
					int leastNum = countConstraints(bestVar, assignment);
					
					// Use most constraining variable heuristic to break ties
					if(iNum > leastNum)
						bestVar = i;
					
					// If there are any more ties, break them alphabetically
					else if(iNum == leastNum && vars.get(i) < vars.get(bestVar))
						bestVar = i;
				}
			}
		}
		
		// Return the best variable
		return bestVar;
	}
	
	/* Returns the number of constraints with the given variable; used in nextVar function
	 *		Input:	Variable (index into vars)	(int var)
	 *
	 *		Output:	The number of constraints	(int)
	 */
	public static int countConstraints(int var, Integer[] assignment)
	{
		int count = 0;
		
		// Loop through constraints
		for(int i = 0; i < cons.size(); i++)
		{
			String[] con = cons.get(i);
			int var1 = Integer.parseInt(con[0]);
			int var2 = Integer.parseInt(con[2]);
			
			// Increment count whenever var appears in a constraint with an unassigned variable
			if(var == var1 && assignment[var2] == null)
				count++;
			else if(var == var2 && assignment[var1] == null)
				count++;
		}
		
		// Return the count
		return count;
	}

	/* Chooses the next value to be assigned to the given variable
	 *		Input:	Variable (index into vars)									(int var)
	 *				List of values that have already been assigned to var		(ArrayList<Integer> prevVals)
	 *				The domain for all the variables							(ArrayList<ArrayList<Integer>> varDomains)
 	 *				The assignment for the variables at the current iteration	(Integer[] assignment)
	 *
	 *		Output:	The value of the variable chosen							(int)
	 */
	public static int nextVal(int var, ArrayList<Integer> prevVals, ArrayList<ArrayList<Integer>> varDomains, Integer[] assignment)
	{
		// Keep track of the number of values remaining for each change made
		int[] numValuesRemaining = new int[varDomains.get(var).size()];
		
		// Loop through all values
		for(int i = 0; i < varDomains.get(var).size(); i++)
		{
			numValuesRemaining[i] = -1;
			
			// Skip values that were already tried
			boolean skip = false;
			for(Integer prevVal : prevVals)
				if(prevVal == varDomains.get(var).get(i))
					skip = true;
			
			// If the value has not yet been assigned to var
			if(!skip)
			{
				// Keep track of the number of values remaining for every unassigned variable when var=val is added
				numValuesRemaining[i] = 0;
				
				// Add var=val to the assignment
				Integer[] tempAssignment = new Integer[assignment.length];
				tempAssignment = assignment.clone();
				tempAssignment[var] = varDomains.get(var).get(i);
	
				// Get the new domain once var=val is added to the assignment
				ArrayList<ArrayList<Integer>> tempVD = adjustVarDomains(var, varDomains, tempAssignment);
				
				// Loop through all unassigned variables and sum the size of their domains
				for(int j = 0; j < vars.size(); j++)
					if(tempAssignment[j] == null)
						numValuesRemaining[i] += tempVD.get(j).size();
			}
		}

		// Loop through all values in the domain of var
		int bestValIndex = -1;
		for(int i = 0; i < varDomains.get(var).size(); i++)
		{
			// Pick the value that is the least constraining
			if(bestValIndex == -1 || numValuesRemaining[i] > numValuesRemaining[bestValIndex])
				bestValIndex = i;
			
			// Break ties by preferring the smaller value
			else if(numValuesRemaining[i] == numValuesRemaining[bestValIndex] && varDomains.get(var).get(i) < varDomains.get(var).get(bestValIndex))
				bestValIndex = i;
		}
		
		// Return the chosen value
		return varDomains.get(var).get(bestValIndex);
	}
	
	/* Adjusts the domain of all variables after a var=val change is applied
	 *		Input:	Variable (index into vars) that was changed					(int changedVar)
	 *				The domain for all the variables							(ArrayList<ArrayList<Integer>> varDomains)
 	 *				The assignment for the variables at the current iteration	(Integer[] assignment)
	 *
	 *		Output:	The new variable domains after adjusting					(ArrayList<ArrayList<Integer>>)
	 */
	public static ArrayList<ArrayList<Integer>> adjustVarDomains(int changedVar, ArrayList<ArrayList<Integer>> varDomains, Integer[] assignment)
	{
		// Copy the variable domains (so we can safely edit them)
		ArrayList<ArrayList<Integer>> tempVarDomains = new ArrayList<ArrayList<Integer>>(vars.size());
		
		for(int i = 0; i < varDomains.size(); i++){
			ArrayList<Integer> domain = new ArrayList<Integer>();
			for(int j = 0; j < varDomains.get(i).size(); j++)
				domain.add(varDomains.get(i).get(j));
			
			tempVarDomains.add(domain);
		}

		// Loop through the constraints
		for(int i = 0; i < cons.size(); i++)
		{
			String[] con = cons.get(i);
			int var1 = Integer.parseInt(con[0]);
			int var2 = Integer.parseInt(con[2]);
			
			// If the variable that was changed is a part of the constraint, it needs to be considered
			if(var1 == changedVar || var2 == changedVar)
			{
				Integer changeVal = assignment[changedVar];
				int other = var1;
				if(var1 == changedVar)
					other = var2;
				
				// Only adjust the domains of unassigned variables
				if(assignment[other] == null)
				{
					if(Objects.equals(con[1], "=")) {
						for(int j = 0; j < tempVarDomains.get(other).size(); j++)
							if(tempVarDomains.get(other).get(j) != changeVal){
								tempVarDomains.get(other).remove(j);
								j--;
							}
					}
					else if(Objects.equals(con[1], "!")) {
						for(int j = 0; j < tempVarDomains.get(other).size(); j++)
							if(tempVarDomains.get(other).get(j) == changeVal){
								tempVarDomains.get(other).remove(j);
								j--;
							}
					}
					else if(Objects.equals(con[1], ">")) {
						// Other variable > Changed variable
						if(other == var1){
							for(int j = 0; j < tempVarDomains.get(other).size(); j++)
								if(tempVarDomains.get(other).get(j) <= changeVal){
									tempVarDomains.get(other).remove(j);
									j--;
								}
						}
						// Other variable < Changed variable
						else{
							for(int j = 0; j < tempVarDomains.get(other).size(); j++)
								if(tempVarDomains.get(other).get(j) >= changeVal){
									tempVarDomains.get(other).remove(j);
									j--;
								}
						}							
					}
					else if(Objects.equals(con[1], "<"))
					{
						// Other variable < Changed variable
						if(other == var1){
							for(int j = 0; j < tempVarDomains.get(other).size(); j++)
								if(tempVarDomains.get(other).get(j) >= changeVal){
									tempVarDomains.get(other).remove(j);
									j--;
								}
						}
						// Other variable > Changed variable
						else{
							for(int j = 0; j < tempVarDomains.get(other).size(); j++)
								if(tempVarDomains.get(other).get(j) <= changeVal){
									tempVarDomains.get(other).remove(j);
									j--;
								}
						}
					}
				}
			}
		}
		
		// Return the new variable domains
		return tempVarDomains;
	}
}
