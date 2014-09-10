%include polycode.fmt
%format `union` = "\cup"
%format /= = "\neq"

\section{Implementation in Haskell}
\label{ch4:sec:implementation}
In this section, we present (some fragments of) an implementation of
\cref{ch4:pmfdclass} in
\emph{Haskell}.\footnote{\href{http://www.haskell.org/}{\url{www.haskell.org}}}
The complete software is included on a CD at the end of the printed copies of
this thesis, and in the near future the code can also be found on the author's
github page.\footnote{%
\href{https://github.com/J0J0/}{\url{www.github.com/J0J0}}%
\;\;(J-zero-J-zero)}
See \cref{ch4:tab:funcs1} at the end of the section for a correspondence between
the presented types/functions and the modules they are defined in.

Our basic types are |Vertex|, |Simplex| and |Complex| that are defined as
follows:
\begin{code}
data Vertex a where Vertex :: (Eq a) => a -> Vertex a

type Simplex a = [Vertex a]

type Complex a = [Simplex a]
\end{code}
A |Vertex| can be basically anything, but we require an |Eq| context
(which should not be much of a restriction). (Note that this declaration
uses a GADT\footnote{generalised algebraic datatype,
\href{http://www.haskell.org/haskellwiki/Generalised_algebraic_datatype}{%
\url{www.haskell.org/haskellwiki/Generalised_algebraic_datatype}}}
to enforce that vertices can be tested for equality.) A \enquote{set}
of vertices is a list in Haskell and likewise for complexes. Of course,
this allows \enquote{simplices with repeated vertices} or similar anomalies,
so it is the programer's job to make sure that such (invalid) complexes
are not passed to the library.

Let $K$ be a finite weak $2$-pseudomanifold. To identify the closed
surfaces~$S_j$ such that $\geom{K} \cong (\coprod_{j=1}^k S_j)/{\sim}$ 
(which exist by \cref{ch4:pmfdclass}) we proceed as follows:
The proof of \cref{ch4:pmfdclass} and the preceding proposition provide us with an
algorithm for identifying a vertex as a singularity and for resolving the
latter. We test each vertex, fix the singularity if necessary and finally
obtain a complex~$K'$ such that $\geom{K'}$ is a compact $2$-manifold. Then
we isolate the connected components of~$K'$ and for each component~$L\subset K'$
we identify the surface~$\geom{L}$. If we are only interested in the closed
surfaces~$S_j$, we are done here, but if we also want to specify how they
are glued together, further examination of~$K'$ is required.

We get back to the gluing problem later and start with the identification
of the surfaces~$S_j$. Assume that $K$ is given as |c :: Complex a| and
that |v :: Vertex a| is a vertex of |c|. Then |fixSingularity v c| returns
a complex with the singularity at (the vertex corresponding to) |v| resolved.
This is the implementation of the function |fixSingularity|:
\begin{code}
fixSingularity :: (Eq a) => Vertex a -> Complex a -> Complex (a, Int)
fixSingularity v c =  let  f   =  id &&& const 0
                           c'  =  complexMap f c
                           v'  =  vMap f v
                      in   fixSingularity' v' c'
 
fixSingularity' ::  (Eq a) =>
                    Vertex (a, Int) -> Complex (a, Int) -> Complex (a, Int)
fixSingularity' v c =
    case starSummands v c of
        _:[]  ->  c
        sSs   ->  fixSingularity'' v sSs c

fixSingularity'' :: {-"\mbox{\small(type omitted for readability)}"-}
fixSingularity'' v sSs c =
    let  sSs' = map (parentSimplices [v] . generatedBy) sSs
         oldSimplices  =  [v] : concatMap (delete [v]) sSs'
         newSimplices  =  concatMap (replaceStarSummand v) $ [1..] `zip` sSs'
    in   (c \\ oldSimplices) `union` newSimplices

{-"\\[-1.2\baselineskip]"-}

starSummands :: Vertex a -> Complex a -> StarSummands a
starSummands = findSummands .: star

findSummands :: Complex a -> StarSummands a
findSummands st =
    case filter (isNSimplex 2) st of
        []   ->  []
        s:_  ->  let
                     summand = dfsSimplices st s
                     st' = st \\ summand
                 in  summand : findSummands st'
\end{code}
To be able to split a vertex into multiple copies (like in the proof of
\cref{ch4:pmfdclass}), we first transform |c| into |c' :: Complex (a, Int)|
where each vertex has the index~$0$ attached. The function |fixSingularity'|
obtains the wedge summands of $\st(v)$ and passes them to |fixSingularity''|
unless there is no singularity at~|v|. The latter function then implements
what is described in the proof of the theorem (where |parentSimplices s c1|
returns all simplices of $c_1$ of which |s| is a face).
The computation of the star summands are quite clear once we explain what
|dfsSimplices| does. \emph{Dfs} is an abbreviation for \emph{depth first
search}, a common algorithm for graph traversal. In this case
|dfsSimplices c1 s1| starts at a simplex $s_1\in c_1$ of dimension~$d$ and
returns all $d$-simplices of~$c_1$ that share a common $(d{-}1)$-dimensional face
with~$s_1$ or another simplex already visited. For instance, |dfsSimplices c s|
for any $2$-simplex~|s| of~|c| returns all $2$-simplices of~|c| if and only if
|c| is strongly connected.

Now assume that we resolved all singularities and that we already called
> connectedComponents :: Complex a -> [Complex a]
on the resulting complex. Thus we are left with the task to identify a surface
complex. This is done by the function |identifySurface| which takes a complex
and has the following return type:
\begin{code}
data Surface = Surface {   isOrientable  ::  Bool,
                           genus         ::  Integer  } deriving (Eq, Ord)
\end{code}
(i.\,e. we uniquely identify a closed surface via orientability
and its genus). Instead of including the implementation of
|identifySurface| here, we only explain how it works. Basically,
there are two approaches that come to mind:
\begin{itemize}[topsep=5pt,labelindent=0pt]
\item
    Determine the orientability type explicitely and calculate the genus from
    the Euler characteristic.
\item
    Compute a \emph{fundamental polygon} of the complex and analyse
    the labelling scheme.
\end{itemize}
Our implementation follows the latter strategy since we need its functionality
in \cref{ch4:sec:latonpmfd} anyway. To be a little bit more specific, we do the
following: paste all $2$-simplices together to obtain a polygon with edges to be
identified in pairs; normalize the resulting labelling scheme; determine the
surface type from the normal form. The whole process, known as the
classification of closed surfaces, can be found in the topology book by
Munkres~\cite[Ch.~12]{bookc:munkres00}.

Put together, the above discussion provides the desired identification of the
closed surfaces~$S_j$. The function
\begin{code}
baseSurfaces :: (Eq a) => Complex a -> [Surface]
baseSurfaces =
    map identifySurface . connectedComponents . fixAllSingularities
\end{code}
composes the functions we met before (respectively a slight variation in case
of |fixAllSingularities|). It takes a complex and yields a list of surfaces,
the~$S_j$ for the particular complex. For instance, assume that |tor| is a
complex that triangulates the torus, |#| denotes connected sum and |\/|
denotes wedge sum. Then we have:
> baseSurfaces tor                   {-"\qquad"-} --  [OS.g=1]
> baseSurfaces $ (tor # tor) \/ tor  {-"\qquad"-} --  [OS.g=2,OS.g=1]
where \enquote{OS.g=r} means \enquote{orientable surface of genus~$r$}.

Now we treat the gluing. Remeber that we have $\geom{K} \cong
(\coprod_{j=1}^k S_j)/{\sim}$ where $\sim$ is an equivalence relation that
identifies only finitely many points. Since the exact relation $\sim$ is
neither topologically relevant nor convenient to work with, we strip the gluing
information down to a \emph{gluing graph}, determined by the following data:
\begin{itemize}[topsep=5pt,labelindent=0pt]
\item
    a set $N_{\mr g}$ of (abstract) gluing nodes,
\item
    the set $N_{\mr s} \defeq \{S_1,\dots,S_k\}$ of surface nodes,
\item
    and a function $e\colon N_{\mr g}\times N_{\mr s}\to\N$ that
    specifies how often a surface is glued to a particular
    gluing point.
\end{itemize}
Note that this defines a (bipartite) multigraph whithout self-loops
(see \cref{ch4:fig:gluinggraph} for an example).
In our implementation we use the following types to store the multigraph
(where |M| and |LM| are the modules @Data.Map.Strict@ and @.Lazy@, respectively):
\begin{code}
type GluingGraphD       =  M.Map (Int,Int) Int
type GluedObj o         =  LM.Map Int o
type GluedVertices  a   =  GluedObj (Vertex a)
type GluedComplexes a   =  GluedObj (Complex (a, Int))
data GluedD a = GluedD {  
                          glGraphD     ::  GluingGraphD
                       ,  glVertices   ::  GluedVertices a
                       ,  glComplexes  ::  GluedComplexes a }
\end{code}
|GluingGraphD| represents the function $e$; a node (of either type) is an |Int|
which is mapped by |GluedVertices| and |GluedComplexes| to the corresponding
object. |GlueD| combines all gluing data that we work with.  To extract that
data from the weak pseudomanifold, we use the next two functions (with
accompanying helpers):
\begin{code}
gluingGraph :: (Eq a) => Complex a -> GluedD a
gluingGraph = gluingGraphFromFixed . fixAllSingularities

gluingGraphFromFixed :: (Eq a) => Complex (a, Int) -> GluedD a
gluingGraphFromFixed c =
    GluedD { glGraphD = graph, {-"\;"-} glVertices = vsm, {-"\;"-} glComplexes = comps }
        where
            comps  =  LM.fromDistinctAscList $ [0..] `zip` connectedComponents c
            vs     =  nub $ map (vMap fst) $ filter isGluedV $ vertices c
            vsi    =  vs `zip` [0..]
            vsm    =  LM.fromDistinctAscList $ map swap vsi
            graph  =  LM.foldrWithKey (addGluingData vsi) M.empty comps

isGluedV :: Vertex (a, Int) -> Bool
isGluedV (Vertex (_,t)) = t /= 0

addGluingData :: {-"\mbox{\small(type omitted for readability)}"-}
addGluingData vsi j comp m =
    foldr (\ v -> M.insertWith (+) (toId v,j) 1) m gluedToVs
        where
            gluedVs    =  filter isGluedV $ vertices comp
            gluedToVs  =  map (vMap fst) gluedVs 
            toId v     =  fromJust $ lookup v vsi
\end{code}
Furthermore, we provide a utility function that extracts the most interesting
parts from a |GluedD|, that is the actual multigraph (as a |GluingGraphD|)
and the glued surfaces (identified as |Surface|):
\begin{code}
type GluedSurfaces  =  GluedObj Surface

gluingGraphSurf :: (Eq a) => Complex a -> (GluingGraphD, GluedSurfaces)
gluingGraphSurf = (glGraphD &&& identifyGluedSurfaces) . gluingGraph

identifyGluedSurfaces :: GluedD a -> GluedSurfaces
identifyGluedSurfaces = LM.map identifySurface . glComplexes
\end{code}
The functions
> writeGluingGraph :: (GluingGraphD, GluedSurfaces) -> FilePath -> IO ()
> visualizeGluingGraph :: (GluingGraphD, GluedSurfaces) -> IO ()
even use the \emph{graphviz} library\footnote{%
\href{http://projects.haskell.org/graphviz/index.html}{%
\url{projects.haskell.org/graphviz/}}} (and the identically
named software\footnote{\href{http://www.graphviz.org/}{%
\url{www.graphviz.org}}})
to export a nice figure of the gluing graph to a png file,
respectively to draw the graph on the screen (using an X11 windowing
system). For example, let |tor| be as above and let |ptor| be a complex that
triangulates the \emph{pinched torus} (i.\,e. $(S^1\times S^1)/
(\{[0]\}\times S^1)$ or, alternatively, a $2$-sphere with two
distinct points identified). Then
>  visualizeGluingGraph $ gluingGraphSurf $ (ptor # ptor) \/ (tor \/ tor)
draws the multigraph in \cref{ch4:fig:gluinggraph}.

\begin{figure}
    \centering
    \includegraphics[width=0.55\textwidth]{figs/gluinggraph}
    \caption{Example of a gluing graph}
    \label{ch4:fig:gluinggraph}
\end{figure}

\begin{table}[ht]
\centering
\begin{tabular}{lp{4.5cm}}
    \textbf{module} & \textbf{types and functions}
    \\[4pt]
    @SimplicialComplex@ & |Vertex|, |Simplex|, |Complex|,   \newline
                          |connectedComponents|,            \newline
                          |dfsSimplices|,                   \newline
                          |parentSimplices|
    \\[3pt]
    @TwoDimPseudoManifold@ & |baseSurfaces|,            \newline
                             |fixSingularity| etc.,     \newline
                             |fixAllSingularities|,     \newline
                             |starSummands| etc.
    \\[3pt]
    @TwoDimManifold@ & |identifySurface|
    \\[3pt]
    @Surface@ & |Surface|
    \\[3pt]
    @TwoDimPseudoManifold.GluingGraph@
        \hspace*{0.8cm}                 & |GluedD| etc.,           \newline
                                          |gluingGraph| etc.       \newline
                                          |gluingGraphSurf| etc.
    \\[3pt]
    @TwoDimPseudoManifold.GraphViz@ & |writeGluingGraph|,       \newline
                                      |visualizeGluingGraph|
\end{tabular}
\caption{Correspondence between presented functions and modules}
\label{ch4:tab:funcs1}
\end{table}


\section{Loop Agreement Tasks on Two-dimensional Pseudomanifolds}
\label{ch4:sec:latonpmfd}
Lastly, we consider loop agreement tasks on finite weak $2$-pseudomanifolds.
We show that the \emph{word problem} for fundamental groups of such $2$-pseudomanifolds
is solvable and use this fact in conjunction with \cref{ch3:classification}
to formulate a result about loop agreement tasks.

It is well known that the word problem for fundamental groups of closed surfaces
is solved by \emph{Dehn's Algorithm}, see
Stillwell~\cite[Sec.~6.1]{bookc:stillwell93}.
Then the following proposition is a consequence of this fact and
\cref{ch4:pmfdclass}.

\begin{thProposition}[solvability of the word problem for %
                      finite weak $2$-pseudomanifold]
    \label{ch4:wordproblem}
    %
    The word problem for the fundamental group of a $2$-dimensional finite weak
    pseudo\-manifold (based at any vertex) is solvable.
\end{thProposition}

\begin{proofsketch}
    First, observe that for finite weak $2$-pseudomanifolds $K,K'$ and vertices
    $v,v'$ of $K$ and $K'$, respectively, we have 
    \[  \pi_1\bigl( (K,v) \topowedge (K',v') \bigr)
            \cong \pi_1(K,v) \ast \pi_1(K',v')
    \]
    by the Seifert-van-Kampen theorem (where the wedge of complexes is defined
    in the obvious way). Secondly, let $K$ be a finite weak $2$-pseudomanifold
    and let $v_1,v_2$ be vertices of $K$ that have disjoint stars.
    Let $K'$ be the resulting complex after identifying $v_1$ and $v_2$ to a
    single vertex $v'$. Then we have
    \[ \pi_1(K',v') \cong \pi_1(K,v_1) \ast \Z , \]
    as can be seen by using the standard construction of the fundamental group
    of a simplicial complex in terms of generators and relations (see e.\,g.
    Herlihy~et~al.~\cite[Subsec.~15.1.2]{bookc:herlihyetal13}
    for the latter).

    Now let $K$ be a finite weak $2$-pseudomanifold, let $v\in V(K)$
    and assume without loss of generality that $K$ is connected.
    By \cref{ch4:pmfdclass} and an inductive application of the above arguments
    we see that $\pi_1(K,v)$ is isomorphic to a free product of the form
    \[ \pi_1(S_1,x_1) \ast \cdots \ast \pi_1(S_k,x_k)
        \ast \underbrace{\Z \ast \cdots \ast \Z}_{\ell\text{ times}}
    \]
    where $S_1,\dots,S_k$ are the closed surfaces of \cref{ch4:pmfdclass},
    $x_j\in S_j$ for all $j\in\setOneto k$, and $\ell\in\N$.
    A reduced word $g_1g_2\dots g_r$ in such a free product is the identity
    element if and only if each $g_j$ is the idendity element in its corresponding group.
    Since we know how to solve the word problem for each free factor
    of~$\pi_1(K,v)$, we also know how to solve it for $\pi_1(K,v)$ itself.
    \\
\end{proofsketch}

\begin{thCorollary}[loop agreement tasks on finite weak 2-pseudomanifolds]
    \label{ch4:latonpmfd}
    %
    Let $K,L\in\finSimp$ and let $\kappa,\lambda$ be triangle loops in $K$ and
    $L$, respectively. Futhermore, let $K$ and $L$ be weak $2$-pseudomanifolds.
    \begin{itemize}
        \item 
            It is decidable whether $\gamma_\kappa$ and $\gamma_\lambda$
            are (pointed) contractible in $\geom{K}$ and $\geom{L}$,
            respectively.
            
        \item
            If $\gamma_\kappa$ is (pointed) contractible,
            it is decidable whether $\Loop{K,\kappa}$ implements $\Loop{L,\lambda}$.
    \end{itemize}
\end{thCorollary}

\begin{proof}
    The first part is immediate from \cref{ch4:wordproblem}. For the second
    part let $\gamma_\kappa$ be pointed  contractible. As a direct consequence, the
    algebraic signature of~$\Loop{K,\kappa}$ is
    \[ (\pi_1(K,\dot\kappa), 1) \]
    (where $1\in\pi_1(K,\dot\kappa)$ denotes the identity element).
    Then \cref{ch3:classification}, the fact that $1$ must be mapped to the
    identity element of~$\pi_1(L,\dot\lambda)$ by any group homomorphism
    $\pi_1(K,\dot\kappa)\to\pi_1(L,\dot\lambda)$, and the first part imply
    the assertion.
    \\
\end{proof}

\medskip
Our Haskell library (see \cref{ch4:sec:implementation}) also includes a
counterpart to the theoretical \cref{ch4:latonpmfd}, that is we provide
a function
>  isTrivial :: (Eq a) => Loop a -> Complex a -> Bool
that tests whether a given loop is contractible on a finite weak
$2$-pseudomanifold. Here a loop is specified as a walk |[Vertex a]| 
\pcref{ch3:def:walkpathcycle} with identical first and last vertex.
(Note that we also permit repeated vertices in this case.)
The main difficulty in implementing |isTrivial| is that we have
to find a representation of the loop in terms of generators and relations
in order to apply the algorithm for solving the word problem. Therefore,
the function has to trace the given loop through the process of building
the fundamental polygon and normalizing it afterwards (as mentioned in the
previous section). Since this is a rather complex procedure, we make no attempt
to explain the corresponding functions |schemesWL| and |normalize|
in detail here. After applying those functions, we get an intermediate
result of type 
> (GluedObj Scheme, LoopS)
where a |Scheme| is just a labelling scheme of a polygon, |GluedObj Scheme|
stores the schemes for our surfaces~$S_j$ (of \cref{ch4:pmfdclass})
and a |LoopS| is a representation of our input loop in terms of the symbols
used in those schemes.
As an example, consider the wedge of two tori. Then the first component of the
above tuple would contain the labelling schemes $aba^{-1}b^{-1}$ and
$cdc^{-1}d^{-1}$ and the second component would be any word in the letters
$\{a,b,c,d\}$ and their formal inverses. For instance,
$abcdc^{-1}d^{-1}a^{-1}b^{-1}$ would specify a contractible loop.

The last step is the implementation of \cref{ch4:wordproblem}. The function
> simplifyLoop :: GluedObj Scheme -> LoopS -> LoopS
takes the data described in the last paragraph and reduces the loop to either
the empty word (in which case the input loop is in fact contractible) or a
word that cannot be further simplified. Depending on the involved surfaces
|simplifyLoop| uses the functions |simplifyOnX| (with |X| one of
$\{\text{|Sphere|}, \text{|Torus|}, \text{|PrPlane|}, \text{|KleinB|}\}$)
and |dehnAlg| to solve the word problem.

The implementation of Dehn's algorithm and the function |dehnAlg| can be found
in the module @DehnAlgorithm@ and all other functions of this section are
defined in @TwoDimPseudoManifold.Loop@.
