(* ::Package:: *)

NotebookDirectory[]


(* CwebGen.m *)

(* Authors: Neelima Agarwal, Sourav Pal, Aditya Srivastav, Anurag Tripathi *)
(* Version: 1.0 (October 2024) *)


BeginPackage["CwebGen`"];

(* Public function and usage declaration *)
availablePublicFunctions::usage = 
    "availablePublicFunctions[] returns a list of public functions available in the CwebGen package.";
(*ColLegInputForm::usage = 
                  "This block changes the input form of color of a diagram from T[1,i,a]**T[2,i,a]**T[2,j,b]**T[3,j,b] to {{T[1,i,a]},{T[2,i,a]**T[2,j,b]},{T[3,j,b]}}  ";
*)
hierarchies::usage = 
                  "For a Cweb with n-correlators it provides all the possible orderings among the correlator indices (replica indices). It takes input colour of a diagram of a web in the form T[1,i,a]**T[2,i,a]**T[2,j,b]**T[3,j,b].... and provides output as a set of n-tuples which are used as hierarchies.";

orderNCoeff::usage = 
                  "It provides O(N) coefficient that is multiplied with the replica ordered colour factor generated for a given hierarchy as input.";

diagramsOfWeb::usage = " This function takes input the colour factor of one diagram and do the shuffle to generate all the diagrams of the web.";

repOrdColour::usage = 
                  "This function is used to calculate the replica ordered colour factor for each diagram of the web subjected a given hierarchy. For the colour of a given diagram and the hierarchy as inputs It provides in the output a colour which is ordered as described by Replica ordering operator with this given hierarchy";


mixingMatrix::usage = 
                  "mixingMatrix[webcolour,ff] computes the mixing matrix, diagonalising matrix and diagonal matrix for a given CWeb. It also provides the checks of Idempotence and Row Sum in the output.";

Begin["`Private`"];


Print["CWebGen.m - A tool to study colour structure of scattering amplitudes in IR limit"];
Print["Authors: Neelima Agarwal, Sourav Pal, Aditya Srivastav, Anurag Tripathi"];
Print["Version: 1.0 (November 2024)"];


(* Private internal blocks *)

PrivateColLegInputForm[PlainColor_]:=Block[{hm,tum,outP,Legs},Legs=DeleteDuplicates[Table[PlainColor[[r,1]],{r,Length[PlainColor]}]];
hm=PlainColor/.NonCommutativeMultiply-> List;
tum=Table[Select[hm,#[[1]]==r&],{r,Legs}];
outP=Table[If[Length[tum[[r]]]>1,List[NonCommutativeMultiply@@tum[[r]]],tum[[r]]],{r,Length[tum]}];Return[outP]]


PrivateHierarcy[numrep_] := 
 Block[{just, start, stepone, step2, step3, Generators, hierarcy}, 
  just = Table[Range[k], {k, numrep}]; start = Tuples[just]; 
  stepone = 
   DeleteDuplicates[Table[Sort[start[[j]]], {j, Length[start]}]] ; 
  step3 = DeleteDuplicates[Table[stepone[[j]], {j, Length[stepone]}]];
   Generators = 
   Complement[
    Table[If[
      Max[DeleteDuplicates[
         Flatten[Table[{Abs[
             step3[[r]][[i]] - step3[[r]][[i + 1]]]}, {i, 
            numrep - 1}]]]] >= 2, Skip, step3[[r]]], {r, 
      Length[step3]}], {Skip}]; 
  hierarcy = 
   Flatten[Table[
     Permutations[Generators[[r]]], {r, Length[Generators]}], 1]; 
  Return[hierarcy];]



PrivateNorderCoe[hi_]  := Block[{nh, Mn, MnorderN}, nh = CountDistinct[hi];
          Mn = Binomial[N, nh];
          MnorderN = (Series[Mn,{N,0,1}]//Normal)/.N-> 1;Return[MnorderN]];



PrivateShuffle[in_, out___] := 
  Join @@ ReplaceList[in, {x___, {a_, b___}, y___} :> PrivateShuffle[{x, {b}, y}, out, a]];

PrivateShuffle[{{} ..}, out__] := {{out}};


PrivaterepOrdColour[DGCol_, H_] := 
  Block[{pick, OuT, QW, Wr, LegOFshuffle, NoshuffleLeg, RpTRKinputleg,
     AssoREPhier, TsAssoHier, RepSortedAssoLeg, ListFormAss, 
    RepSortedCol, sortWOTB, LegNUM, repNUM, Outp, Final}, 
   LegNUM = 
    DeleteDuplicates[Table[DGCol[[r, 1]], {r, Length[DGCol]}]]; 
   repNUM = 
    DeleteDuplicates[Table[DGCol[[r, 2]], {r, Length[DGCol]}]]; 
   pick = ReverseSort[DeleteDuplicates[H]]; 
   QW = Normal[Counts[Table[DGCol[[r, 1]], {r, Length[DGCol]}]]];  
   Wr = DeleteCases[QW, x_ -> 1] /. Rule -> List; 
   LegOFshuffle = First /@ Wr;
   NoshuffleLeg = Complement[LegNUM, LegOFshuffle];
   Do[RpTRKinputleg[r] = Select[DGCol, #[[1]] == r &], {r, 
     LegOFshuffle}]; 
   AssoREPhier = 
    Association[Table[repNUM[[r]] -> H[[r]], {r, Length[repNUM]}]]; 
   Do[TsAssoHier[r] = 
     Table[RpTRKinputleg[r][[ed]] -> 
       AssoREPhier[RpTRKinputleg[r][[ed, 2]]], {ed, 
       Length[RpTRKinputleg[r]]}], {r, LegOFshuffle}]; 
   Do[ListFormAss[rd] = Normal[TsAssoHier[rd]] /. Rule -> List, {rd, 
     LegOFshuffle}];
   Do[RepSortedAssoLeg[rd] = 
     Flatten[Table[Select[ListFormAss[rd], #[[2]] == v &], {v, pick}],
       1], {rd, LegOFshuffle}];
   
   Do[RepSortedCol[rc] = 
     Table[RepSortedAssoLeg[rc][[r]][[1]], {r, 
       Length[RepSortedAssoLeg[rc]]}], {rc, LegOFshuffle}];
   
   
   Do[RepSortedCol[NoshuffleLeg[[t]]] = 
     Select[Table[
       DGCol[[r]], {r, Length[DGCol]}], #[[1]] == 
        NoshuffleLeg[[t]] &], {t, Length[NoshuffleLeg]}];
   
   
   OuT[0] = Flatten[Table[RepSortedCol[rc], {rc, LegNUM}]] ;
   Return[Apply[NonCommutativeMultiply, OuT[0]]];];


PrivatemixingMatrix[wEB_, ff_] := 
  Block[{InputformCol,idemp,rowsum,ColLeg, AA, CD, MnorderN, Mn, allDGRMS, hierLen, Ctilde, 
    ForDiag, DGnum, hira, LEGcols, nh, CDarray, LegNUM, repNUM, 
    DiagHColor,dir, Rarray, outPUT, outPUTR, rank, DCdgrms, dddd, p,  pc,
     pd, ecf, ecf1, ecfarray, rule1, rule2 , printdiagrams,
   rankandR,Ymatrix,ECFs}, InputformCol = ColLegInputForm[wEB];
   Do[ColLeg[hj] = InputformCol[[hj]], {hj, Length[InputformCol]}];
   LEGcols = 
    Table[If[Head[ColLeg[gh][[1]]] === NonCommutativeMultiply, 
      Table[ColLeg[gh][[1, rt]], {rt, 
        Length[ColLeg[gh][[1]]]}], {ColLeg[gh][[1]]}], {gh, 
      Length[InputformCol]}]; AA = Flatten[LEGcols];
   LegNUM = DeleteDuplicates[Table[AA[[gf]][[1]], {gf, Length[AA]}]];
   repNUM = DeleteDuplicates[Table[AA[[gf]][[2]], {gf, Length[AA]}]];
   allDGRMS = 
    Table[DGRMcolWEB[InputformCol][[r]], {r, Length[DGRMcolWEB[InputformCol]]}];
   hira = Hierarcy[Length[repNUM]];
   hierLen = Length[hira];
   DGnum = Length[allDGRMS];
   Do[DiagHColor[dd][hi] = 
     If[CountDistinct[hira[[hi]]] == 1, allDGRMS[[dd]], 
      repOrdColour[allDGRMS[[dd]], hira[[hi]]]], {hi, 1, hierLen}, {dd,
      1, DGnum}];
   CDarray = Table[CD[rr], {rr, DGnum}];
   rule1 = T[n_, i_, a_] -> T[n, a];
   rule2 = (u_?NumericQ a_) ** b_ -> u (a ** b);
   Do[ForDiag[dd][hi] = 
     CD[Flatten[Position[allDGRMS, DiagHColor[dd][hi]]][[1]]]*
      NorderCoe[hira[[hi]]], {hi, 1, hierLen}, {dd, 1, DGnum}];
   Do[Ctilde[dd] = Table[ForDiag[dd][hi], {hi, hierLen}], {dd, DGnum}];
   Rarray = Table[Total[Ctilde[dd]], {dd, 1, DGnum}];
   outPUTR = Normal[CoefficientArrays[Rarray, CDarray]][[2]];
   rank = MatrixRank[outPUTR];
   DCdgrms = allDGRMS;
   dddd = DiagonalMatrix[Eigenvalues[outPUTR]];
   p = Eigenvectors@Transpose[outPUTR];
   (*diagonalMatrix=p.outPUTR.Inverse[p]//MatrixForm;*)
   
   pc = p.CDarray;
   pd = p.DCdgrms;
   Do[ecf1[r] = pd[[r]] ** ff //. rule1, {r, 1, rank}];
   Do[ecf[r] = Distribute[ecf1[r]] /. rule2, {r, 1, rank}];
   ecfarray = Array[ecf, {rank}];
   If[DirectoryQ[NotebookDirectory[]<>"results/"], DeleteDirectory[NotebookDirectory[]<>"results/", DeleteContents -> True]];
   CreateDirectory[NotebookDirectory[]<>"results/"];
   rankandR=List[rank,outPUTR];
   Ymatrix=p;
   ECFs=ecfarray;
Export[NotebookDirectory[]<>"results/"<>"/R.m" , rankandR];
Export[NotebookDirectory[]<>"results/"<>"/Y.m" , Ymatrix];
Export[NotebookDirectory[]<>"results/"<>"/ECFs.m" , ECFs];
Export[NotebookDirectory[]<>"results/"<>"/diagrams.m" , allDGRMS];
rowsum=Table[Total[outPUTR[[qd]]],{qd,Length[outPUTR]}];
idemp=TrueQ[outPUTR.outPUTR==outPUTR];
Print["Idempotence =", idemp];
Print["Row Sum =", rowsum];
   Return["diagrams, R, Y, and ECFs are saved in results directory"]];


ColLegInputForm[PlainColor_]:= PrivateColLegInputForm[PlainColor];

Hierarcy[numrep_] := PrivateHierarcy[numrep];

NorderCoe[hi_] := PrivateNorderCoe[hi];

   (* Main public function *)
PrivateDGRMcolWEB[webs_] := 
  Block[{ColLeg, LEGcols, AA, LegNUM, repNUM, Colrep, InputShuffle, 
    ReplicaShuffle, lll, indexList, iteratar, result}, 
    
    (* Initialize ColLeg with input webs *)
    Do[ColLeg[hj] = webs[[hj]], {hj, Length[webs]}]; 
    
    (* Extract the legs and color structure *)
    LEGcols = 
      Table[If[Head[ColLeg[gh][[1]]] === NonCommutativeMultiply, 
        Table[ColLeg[gh][[1, rt]], {rt, Length[ColLeg[gh][[1]]]}], 
        {ColLeg[gh][[1]]}], {gh, Length[webs]}]; 
    
    (* Flatten and get unique LegNUM and repNUM *)
    AA = Flatten[LEGcols]; 
    LegNUM = DeleteDuplicates[Table[AA[[gf]][[1]], {gf, Length[AA]}]]; 
    repNUM = DeleteDuplicates[Table[AA[[gf]][[2]], {gf, Length[AA]}]]; 
    
    (* Initialize Colrep with empty lists *)
    Do[Colrep[leg][rep] = {}, {leg, LegNUM}, {rep, repNUM}]; 
    
    (* Fill Colrep based on the input *)
    Do[If[AA[[leng]][[1]] === leG && AA[[leng]][[2]] === Rep, 
      AppendTo[Colrep[leG][Rep], AA[[leng]]]], {leng, 1, Length[AA]}, 
      {leG, LegNUM}, {Rep, repNUM}]; 
    
    (* Set InputShuffle for each leg *)
    Do[InputShuffle[lEG] = Table[Colrep[lEG][reP], {reP, repNUM}], 
      {lEG, LegNUM}]; 
    
    (* Shuffle for each leg using the private shuffle function *)
    lll = Max[LegNUM];
    Do[ReplicaShuffle[LEG] = PrivateShuffle[InputShuffle[LEG]], 
      {LEG, LegNUM}];
    
    (* Create index list *)
    indexList = Table[ToExpression["x" <> ToString[ij]], {ij, lll}];
    
    (* Create the actual table expression programmatically *)
    result = Table[
      NonCommutativeMultiply @@ 
        Join @@ Table[ReplicaShuffle[ia][[indexList[[ia]]]], {ia, lll}],
      Evaluate[Sequence @@ Table[{indexList[[ia]], Length[ReplicaShuffle[ia]]}, {ia, lll}]]
    ];
    
    (* Return the result *)
    Return[result // Flatten]
  ];
  
DGRMcolWEB[webs_] :=PrivateDGRMcolWEB[webs];
                          


repOrdColour[DGCol_, H_] := PrivaterepOrdColour[DGCol, H];


mixingMatrix[wEB_, ff_] := PrivatemixingMatrix[wEB, ff];

availablePublicFunctions[] := Names["CwebGen`*"]



(***********Stand Alone*****************************)



hierarchies[wEB_] := 
 Block[{InputformCol,ColLeg,LEGcols,AA,LegNUM,repNUM, just, start, stepone, step2, step3, Generators, hierarcy}, InputformCol = PrivateColLegInputForm[wEB];
   Do[ColLeg[hj] = InputformCol[[hj]], {hj, Length[InputformCol]}];
   LEGcols = 
    Table[If[Head[ColLeg[gh][[1]]] === NonCommutativeMultiply, 
      Table[ColLeg[gh][[1, rt]], {rt, 
        Length[ColLeg[gh][[1]]]}], {ColLeg[gh][[1]]}], {gh, 
      Length[InputformCol]}]; AA = Flatten[LEGcols];
   LegNUM = DeleteDuplicates[Table[AA[[gf]][[1]], {gf, Length[AA]}]];
   repNUM = DeleteDuplicates[Table[AA[[gf]][[2]], {gf, Length[AA]}]];
  just = Table[Range[k], {k, Length[repNUM]}]; start = Tuples[just]; 
  stepone = 
   DeleteDuplicates[Table[Sort[start[[j]]], {j, Length[start]}]] ; 
  step3 = DeleteDuplicates[Table[stepone[[j]], {j, Length[stepone]}]];
   Generators = 
   Complement[
    Table[If[
      Max[DeleteDuplicates[
         Flatten[Table[{Abs[
             step3[[r]][[i]] - step3[[r]][[i + 1]]]}, {i, 
            Length[repNUM] - 1}]]]] >= 2, Skip, step3[[r]]], {r, 
      Length[step3]}], {Skip}]; 
  hierarcy = 
   Flatten[Table[
     Permutations[Generators[[r]]], {r, Length[Generators]}], 1]; 
  Return[hierarcy];]




  
diagramsOfWeb[webcol_] := 
  Block[{ColLeg, LEGcols, AA,webs, LegNUM, repNUM, Colrep, InputShuffle, 
    ReplicaShuffle, lll, indexList, iteratar, result}, 
    webs=PrivateColLegInputForm[webcol];
    (* Initialize ColLeg with input webs *)
    Do[ColLeg[hj] = webs[[hj]], {hj, Length[webs]}]; 
    
    (* Extract the legs and color structure *)
    LEGcols = 
      Table[If[Head[ColLeg[gh][[1]]] === NonCommutativeMultiply, 
        Table[ColLeg[gh][[1, rt]], {rt, Length[ColLeg[gh][[1]]]}], 
        {ColLeg[gh][[1]]}], {gh, Length[webs]}]; 
    
    (* Flatten and get unique LegNUM and repNUM *)
    AA = Flatten[LEGcols]; 
    LegNUM = DeleteDuplicates[Table[AA[[gf]][[1]], {gf, Length[AA]}]]; 
    repNUM = DeleteDuplicates[Table[AA[[gf]][[2]], {gf, Length[AA]}]]; 
    
    (* Initialize Colrep with empty lists *)
    Do[Colrep[leg][rep] = {}, {leg, LegNUM}, {rep, repNUM}]; 
    
    (* Fill Colrep based on the input *)
    Do[If[AA[[leng]][[1]] === leG && AA[[leng]][[2]] === Rep, 
      AppendTo[Colrep[leG][Rep], AA[[leng]]]], {leng, 1, Length[AA]}, 
      {leG, LegNUM}, {Rep, repNUM}]; 
    
    (* Set InputShuffle for each leg *)
    Do[InputShuffle[lEG] = Table[Colrep[lEG][reP], {reP, repNUM}], 
      {lEG, LegNUM}]; 
    
    (* Shuffle for each leg using the private shuffle function *)
    lll = Max[LegNUM];
    Do[ReplicaShuffle[LEG] = PrivateShuffle[InputShuffle[LEG]], 
      {LEG, LegNUM}];
    
    (* Create index list *)
    indexList = Table[ToExpression["x" <> ToString[ij]], {ij, lll}];
    
    (* Create the actual table expression programmatically *)
    result = Table[
      NonCommutativeMultiply @@ 
        Join @@ Table[ReplicaShuffle[ia][[indexList[[ia]]]], {ia, lll}],
      Evaluate[Sequence @@ Table[{indexList[[ia]], Length[ReplicaShuffle[ia]]}, {ia, lll}]]
    ];
    
    (* Return the result *)
    Return[result // Flatten]
  ];

repOrdColour[DGCol_, H_] := 
  Block[{pick, OuT, QW, Wr, LegOFshuffle, NoshuffleLeg, RpTRKinputleg,
     AssoREPhier, TsAssoHier, RepSortedAssoLeg, ListFormAss, 
    RepSortedCol, sortWOTB, LegNUM, repNUM, Outp, Final}, 
   LegNUM = 
    DeleteDuplicates[Table[DGCol[[r, 1]], {r, Length[DGCol]}]]; 
   repNUM = 
    DeleteDuplicates[Table[DGCol[[r, 2]], {r, Length[DGCol]}]]; 
   pick = ReverseSort[DeleteDuplicates[H]]; 
   QW = Normal[Counts[Table[DGCol[[r, 1]], {r, Length[DGCol]}]]];  
   Wr = DeleteCases[QW, x_ -> 1] /. Rule -> List; 
   LegOFshuffle = First /@ Wr;
   NoshuffleLeg = Complement[LegNUM, LegOFshuffle];
   Do[RpTRKinputleg[r] = Select[DGCol, #[[1]] == r &], {r, 
     LegOFshuffle}]; 
   AssoREPhier = 
    Association[Table[repNUM[[r]] -> H[[r]], {r, Length[repNUM]}]]; 
   Do[TsAssoHier[r] = 
     Table[RpTRKinputleg[r][[ed]] -> 
       AssoREPhier[RpTRKinputleg[r][[ed, 2]]], {ed, 
       Length[RpTRKinputleg[r]]}], {r, LegOFshuffle}]; 
   Do[ListFormAss[rd] = Normal[TsAssoHier[rd]] /. Rule -> List, {rd, 
     LegOFshuffle}];
   Do[RepSortedAssoLeg[rd] = 
     Flatten[Table[Select[ListFormAss[rd], #[[2]] == v &], {v, pick}],
       1], {rd, LegOFshuffle}];
   
   Do[RepSortedCol[rc] = 
     Table[RepSortedAssoLeg[rc][[r]][[1]], {r, 
       Length[RepSortedAssoLeg[rc]]}], {rc, LegOFshuffle}];
   
   
   Do[RepSortedCol[NoshuffleLeg[[t]]] = 
     Select[Table[
       DGCol[[r]], {r, Length[DGCol]}], #[[1]] == 
        NoshuffleLeg[[t]] &], {t, Length[NoshuffleLeg]}];
   
   
   OuT[0] = Flatten[Table[RepSortedCol[rc], {rc, LegNUM}]] ;
   Return[Apply[NonCommutativeMultiply, OuT[0]]];];


orderNCoeff[hi_]  := Block[{nh, Mn, MnorderN}, nh = CountDistinct[hi];
          Mn = Binomial[N, nh];
          MnorderN = (Series[Mn,{N,0,1}]//Normal)/.N-> 1;Return[MnorderN]];

End[]; (* End of `Private` context *)
EndPackage[];

