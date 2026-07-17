#-

* Sort-dominated benchmark, in which each term generated merges with terms
* produced across the whole expression. Thus the terms are finalised in the
* last stage of the sorting, and the expression doesn't become trivial as in
* the other sort test.

Symbol x,y,n;
CFunction acc,sum,f;

#procedure sort2test(N,ITERS)
	Local test = - acc(`N'^2*(1+`N')^2/4)
		#do i = 1,`N'
			+ x^`i' * acc(sum(n,1,`N',y^n))
		#enddo
		;
	.sort:setup-0;
	Argument acc;
		Identify sum(?a) = sum_(?a);
	EndArgument;
	.sort:setup-1;

	PolyFun acc;
	#do i = 1,`ITERS'
		#do var = {x,y}
			Identify acc(n?$tmp) = 1;
			PutInside acc `var';
			Multiply $tmp;
			ModuleOption,local $tmp;
			.sort:acc `var' `i'/`ITERS';
		#enddo
	#enddo
	
*	Check result
	Identify x^n?pos_ = n;
	Argument acc;
		Identify y^n?pos_ = n;
	EndArgument;
	.sort
	
	#if `ZERO_test' == 0
		#message Error in sort-2-small.frm
		#terminate
	#endif
#endprocedure

