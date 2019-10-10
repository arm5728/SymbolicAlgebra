;Helper for solve
(defn solveb [e v d]
	(if (= (lhs e) v) 
		e
		(if (= (rhs e) v)
			(list '= (rhs e) (lhs e))
			(if (seq? (rhs e))
				(cond
					(= (op (rhs e)) '*)
						(concat
							(solveb (list '= (list '/ (lhs e) (lhs (rhs e))) (rhs (rhs e))) v 0)
							(solveb (list '= (list '/ (lhs e) (rhs (rhs e))) (lhs (rhs e))) v 0)
						) 
					(= (op (rhs e)) '+)
						(concat
							(solveb (list '= (list '- (lhs e) (lhs (rhs e))) (rhs (rhs e))) v 0)
							(solveb (list '= (list '- (lhs e) (rhs (rhs e))) (lhs (rhs e))) v 0)
						) 
					(and (= (op (rhs e)) '-) (= (length (rhs e)) 3))
						(concat
							(solveb (list '= (list '- (lhs (rhs e)) (lhs e)) (rhs (rhs e))) v 0)
							(solveb (list '= (list '+ (lhs e) (rhs (rhs e))) (lhs (rhs e))) v 0)
						)
					(= (op (rhs e)) '/)
						(concat
							(solveb (list '= (list '* (lhs e) (rhs (rhs e))) (lhs (rhs e))) v 0)
							(solveb (list '= (list '/ (lhs (rhs e)) (lhs e)) (rhs (rhs e))) v 0)
						)
					(= d 1) ;Been here
						nil
					(and (= (op (rhs e)) '-) (= (length (rhs e)) 2)) ;Unary minus
						(solveb (list '= (list '- (lhs e)) (lhs (rhs e))) v 1)
					(= (op (rhs e)) 'exp)
						(solveb (list '= (list 'log (lhs e)) (lhs (rhs e))) v 1)
					(= (op (rhs e)) 'sqrt)
						(solveb (list '= (list 'expt (lhs e) 2) (lhs (rhs e))) v 1)
					(= (op (rhs e)) 'log)
						(solveb (list '= (list 'exp (lhs e)) (lhs (rhs e))) v 1)
					(= (op (rhs e)) 'expt)
						(solveb (list '= (list 'sqrt (lhs e)) (lhs (rhs e))) v 1)
				)
				nil
			)
		)
	)
)

;Solve equation 'e' for value 'v'
(defn solve [e v]
	(solveb e v 0)
)

;Evaluate algebraic equation 'tree' using values in map 'bindings'
(defn myevalb [tree bindings]
	(if (cons? tree)
		(cond
			(and (= (first tree) '-) (= 2 (length tree)))
				(* -1 (myevalb (lhs tree) bindings))
			(= (first tree) 'expt)
				(expt (myevalb (lhs tree) bindings) (myevalb (rhs tree) bindings))
			(= (first tree) 'sqrt)
				(Math/sqrt (myevalb (lhs tree) bindings))
			(= (first tree) 'exp)
				(Math/exp (myevalb (lhs tree) bindings))
			(= (first tree) 'log)
				(Math/log (myevalb (lhs tree) bindings))
			:else
				(@(resolve (symbol (first tree))) (myevalb (lhs tree) bindings)(myevalb (rhs tree) bindings))
		)
		(if (number? tree)
			tree
			(second (assocl tree bindings))
		)
	)
)

;Helper for set-difference
(defn set-differencetrb [x y answer]
  (if (empty? x)
  	answer
  	(set-differencetrb (rest x) y
  		(if-not (member (first x) y)
			(cons (first x) answer)
			answer))))

;Set-difference two sets
(defn set-difference [x y] (set-differencetrb x y '()))

;Return list of vars in expression
(defn vars [expr]
	(if (list? expr)
		(if (empty? expr)
			nil
			(union (vars (lhs expr)) (vars (rhs expr)))
		)
		(if (symbol? expr)
			(list expr)
			nil
		)
	)
)

;Solve equations for variable using map values
(defn solveit [equations variable values]
	(myevalb 
		(rhs 
			(solve 
				(nth equations 
					(.indexOf 
						(map #(set-difference 
							(concat 
								(map first values) 
								(list variable)
							) 
							%) 
							(map vars equations)
						) 
						()
					)
				) 
				variable
			)
		) 
		values
	)
)

;Find unkonwns in map
(defn unknowns [equation values]
	(length (set-difference (vars equation) (map first values)))
)

;Solve for variable using values, test for all equations
(defn solveqns [eqns values variable]
	(if-not (= (second (assocl variable values)) nil)
		(second (assocl variable values))
		(let [indexFunToCheck (.indexOf (map #(unknowns % values) eqns) 1)]
			(let [unknownVar (first (set-difference (vars (nth eqns indexFunToCheck)) (map first values)))]
				(if (= indexFunToCheck -1)
					nil
					(solveqns eqns (concat values (list (list unknownVar 
						(myevalb
							(rhs 
								(solve 
									(nth eqns indexFunToCheck)
									unknownVar
								)
							)
							values
						)))) 
					variable)
				)
			)
		)
	)
)

;Find unknowns in list
(defn unknowns2 [equation knowns]
	(length (set-difference (vars equation) knowns))
)

;Return list of equations needed to solve for var
(defn solveqnsc [codelist equations knowns var]
	(if (some #{var} knowns)
		codelist
		(let [indexFunToCheck (.indexOf (map #(unknowns2 % knowns) equations) 1)]
			(let [unknownVar (first (set-difference (vars (nth equations indexFunToCheck)) knowns))]
				(solveqnsc 
					(cons 
						(solve 
							(nth equations indexFunToCheck) 
							unknownVar
						) 
						codelist 
					)
					equations 
					(cons unknownVar knowns) 
					var
				)
			)
		)
	)
)

;Filter dead code from solveqnsc
(defn filtercode [codelist needed]
	(if-not (cons? codelist)
		'()
		(let [function (first codelist)]
			(if (some #{(lhs function)} needed)
				(concat (list function) (filtercode (rest codelist) (union needed (vars (rhs function)))))
				(filtercode (rest codelist) needed)
			)
		)
	)
)
;Get operator precedence
(defn getPrecedence [operator]
	(if (or (= operator '+)(= operator '-))
		5
		(if (or (= operator '/)(= operator '*)(= operator 'exp)(= operator 'sqrt)(= operator 'expt))
			6
			(if (= operator '=)
				1		
			)
		)
	)
)

;Transform clojure code to java code
(defn tojavab [tree precedence]
	(if (cons? tree)
		(if (= 2 (length tree))
			(cond
				(= (op tree) '-)
					(str 
						"("   (op tree) 
						(tojavab (lhs tree)(getPrecedence (op tree))) ")"
					)
				(= (op tree) 'sqrt)
					(str 
						"Math.sqrt(" 
						(tojavab (lhs tree)(getPrecedence (op tree))) ")"
					)
				(= (op tree) 'exp)
					(str 
						"Math.pow(" 
						(tojavab (lhs tree)(getPrecedence (op tree))) ", 2)"
					)				
			)
			(if-not (= (op tree) 'expt)
				(if (> precedence (getPrecedence (op tree)))
					(str 
						"(" (tojavab (lhs tree)(getPrecedence (op tree))) 
						" " (op tree) " " 
						(tojavab (rhs tree)(getPrecedence (op tree))) ")" 
					)	
					(str 
						(tojavab (lhs tree)(getPrecedence (op tree))) 
						" " (op tree) " " 
						(tojavab (rhs tree)(getPrecedence (op tree)))
					)	
				)
				(str 
					"Math.pow(" (tojavab (lhs tree)(getPrecedence (op tree))) 
					", "
					(tojavab (rhs tree)(getPrecedence (op tree))) ")" 
				)
			)
		)
		tree		
	)
)

;To java wrapper
(defn tojava [tree]
	(str "double " (tojavab tree 0) ";" )
)

;Get java header
(defn arglist [inputs]
	(if (cons? inputs)
		(str "double " (first inputs) (if (> (length inputs)  1) ", " ")") (arglist (rest inputs)))
		nil
	)	
)

;Print java methods
(defn solvecode [funName equations inputs var]
	(doseq [item 
		(concat 
			(list (str "public static double " funName "(" (arglist inputs) " {"))
			(let [filteredEquations (reverse (filtercode (solveqnsc '() equations inputs var) (list var)))]
				(map tojava filteredEquations)
			)
			(list (str "return " var ";"))
			(list (str "}"))
		)] 
		(println item)
	)
)
