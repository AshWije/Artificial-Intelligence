/* Main.java
 * 
 * 		Compile with: 	'javac Main.java'
 * 		Run with: 		'java Main <kb-file>'
 * 
 *		Description:	A theorem prover for clause logic using the resolution principle.
 */

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Scanner;

public class Main {
	
	public static void main(String[] args) throws FileNotFoundException {
		// Make sure the correct number of arguments are provided
		if(args.length == 1)
		{
			String kbFile = args[0];
			
			// Get the clauses from the kb file
			Scanner sc1 = new Scanner(new File(kbFile));

			// Initialize an ArrayList for the kb clauses
			ArrayList<ArrayList<String>> kb = new ArrayList<ArrayList<String>>();
			
			// Loop through lines and add to kb
			while(sc1.hasNextLine()) {
				String next = sc1.nextLine();
				if(!next.trim().isEmpty()) {
					String[] splitLine = next.split("\\s+");
					ArrayList<String> line = new ArrayList<String>();
					for(int i = 0; i < splitLine.length; i++)
						line.add(splitLine[i]);
					kb.add(line);
				}
			}
			sc1.close();
			
			// Negate last clause
			ArrayList<String> lastClause = kb.get(kb.size()-1);
			kb.remove(kb.size()-1);
			for(int i = 0; i < lastClause.size(); i++)
			{
				String atom = lastClause.get(i);
				ArrayList<String> newLine = new ArrayList<String>();
				if (atom.charAt(0) == '~')
					newLine.add(atom.substring(1));
				else
					newLine.add("~"+atom);
				kb.add(newLine);
			}

			
			// Print initial kb clauses and sort alphabetically 
			for(int i = 0; i < kb.size(); i++)
			{
				System.out.print((i+1) + ". ");
				for(int j = 0; j < kb.get(i).size(); j++) {
					System.out.print(kb.get(i).get(j) + " ");
				}
				System.out.println("{}");
				Collections.sort(kb.get(i));
			}
			
			// Apply resolution
			resolution(kb);
		}
		
		// Output a message if the incorrect number of arguments is provided
		else
			System.out.println("Incorrect number of arguments. Execute with: 'java Main <kb-file>'");
	}

	public static boolean resolution(ArrayList<ArrayList<String>> kb)
	{
		// Loop through kb clauses
		for(int i = 1; i < kb.size(); i++)
		{
			ArrayList<String> clause1 = kb.get(i);
			
			// Loop through kb clauses before clause1
			for(int k = 0; k < i; k++)
			{
				ArrayList<String> clause2 = kb.get(k);
				
				// Loop through atoms in clause1
				for(int j = 0; j < clause1.size(); j++)
				{
					// Check if clause1 is negated
					boolean cl1Negated = false;
					if (clause1.get(j).charAt(0) == '~')
						cl1Negated = true;

					// Loop through atoms in clause2
					for(int l = 0; l < clause2.size(); l++)
					{
						// Check if clause1 == ~clause2
						if ((cl1Negated && clause1.get(j).substring(1).equals(clause2.get(l))) ||
								(!cl1Negated && clause2.get(l).length() > 1 && clause2.get(l).substring(1).equals(clause1.get(j))))
						{
							// Create new clause by combining clause1 and clause2
							ArrayList<String> newClause = new ArrayList<String>();
							for(int m = 0; m < clause1.size(); m++)
								if(m != j && !newClause.contains(clause1.get(m)))
									newClause.add(clause1.get(m));
							for(int m = 0; m < clause2.size(); m++)
								if(m != l && !newClause.contains(clause2.get(m)))
									newClause.add(clause2.get(m));

							// If new clause is always true (p ~p), do not add it to the kb
							boolean alwaysTrue = false;
							for(int m = 0; m < newClause.size() && !alwaysTrue; m++)
							{
								boolean negated = false;
								if (newClause.get(m).charAt(0) == '~')
									negated = true;
								if ((negated && newClause.contains(newClause.get(m).substring(1))) || (!negated && newClause.contains("~"+newClause.get(m))))
									alwaysTrue = true;
							}
							if (!alwaysTrue)
							{
								// Alphabetically sort the new clause
								Collections.sort(newClause);
								
								// If the new clause is unique to the kb, add it
								if (!kb.contains(newClause))
								{
									kb.add(newClause);
									
									// If an empty clause is generated, we have found a contradiction
									if(newClause.size() == 0) {
										System.out.println((kb.size()) + ". Contradiction {"+(i+1)+", "+(k+1)+"}\nValid");
										return true;
									}
									
									// Print the new clause
									System.out.print((kb.size()) + ". ");
									for(int m = 0; m < newClause.size(); m++)
										System.out.print(newClause.get(m) + " ");
									System.out.println("{"+(i+1)+", "+(k+1)+"}");
								}
							}
						}
					}
				}
			}
		}
		
		// Print failure if no contradictions were found
		System.out.println("Failure");
		return false;
	}
}
