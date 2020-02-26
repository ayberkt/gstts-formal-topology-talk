\documentclass[leqno]{beamer}
\usetheme{metropolis}
\usepackage{wasysym}
\usepackage{ebproof}

\newcommand{\pity}[3]{\prod_{(#1~:~#2)} #3}
\newcommand{\sigmaty}[3]{\sum_{(#1~:~#2)} #3}
\newcommand{\univ}{\mathsf{Type}}
\newcommand{\rulename}[1]{\textsf{\color{blue} #1}}
\newcommand{\pow}[1]{\mathcal{P}\left( #1 \right)}
\newcommand{\trunc}[1]{\left\| #1 \right\|}
\newcommand{\abs}[1]{\left| #1 \right|}
\newcommand{\bj}{\mathbf{j}}
\newcommand{\is}{:\equiv}

\setmonofont{PragmataPro Mono Liga}
\usepackage{agda}

\title{Formal Topology in Univalent Foundations}

\date{February 27, 2020}
\author{Ayberk Tosun}
\institute{Chalmers University of Technology}

\begin{document}

\maketitle

%% Slide I.
%% · We start out with the simple question of doing topology in type theory.
%% · We need to understand it not only constructively but also predicatively.
%% · To understand it constructively, we formulate topology without the points.
%% · To understand it predicatively, we resort to _formal_ topology in which we try to
%%   write down a topology as though it were a rule-based formal proof system.
%% Mention that the predicativity problem was solved in traditional formal topology, but
%% in univalent foundations there is a problem and this talk focuses on that.
\begin{frame}{Motivation}
  \begin{align*}
    \text{{\huge Top}}&\text{{\huge ology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{constructively}} \\
    \text{{\huge Pointles}}&\text{{\huge s~topology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{predicatively}} \\
    \text{{\huge Forma}}&\text{{\huge l~topology}}\\
  \end{align*}
\end{frame}

%% Slide II.
%% · In pointless topology, we work with algebraic structures generalising the lattice of
%%   open sets of a topological space.
%% · They can be viewed as embodying a logic of propositions that can be verified through
%%   finite evidence, which in CS we take to mean semi-decidability. Unfortunately, I do
%%   not have time to go in depth into this.
%% · Also, as Abramsky called it, they are some kind of junior-grade toposes. Many
%%   theorems of topos theory, are generalisations of theorems of locale theory.
\begin{frame}{What locales are like}
  \begin{itemize}
    \item<1-> Abstraction of open sets of a topology.
    \item<1-> Logic of ``observable properties''.
    \item<1-> CS view: logic of ``semidecidable properties''.
    \item<2> ``Junior-grade topos theory''.
  \end{itemize}
\end{frame}

%% Slide 1.
%% · A frame is nothing but a poset that has all finite meets, all joins, and satisfies
%%   the following distributivity law. In point-set topology, this is justified
%%   set-theoretically but as we abstract we have to account for it explicitly.
\begin{frame}{Locales}
  A poset $\mathcal{O}$ such that
  \begin{itemize}
    \item \alert{finite subsets} of $\mathcal{O}$ have \alert{meets},
    \item \alert{all subsets} of $\mathcal{O}$ have \alert{joins}, and
    \item binary meets distribute over arbitrary joins:
      \begin{equation*}
        a \wedge \left( \bigvee_{i~\in~I} b_i \right) = \bigvee_{i~\in~I} \left( a \wedge b_i \right),
      \end{equation*}
      for any $a \in \mathcal{O}$ and $I$-indexed family $b$ over $\mathcal{O}$.
  \end{itemize}
\end{frame}

%% Slide 2.
%% · One example of a frame is the frame constructed by taking poset and constructing its
%%   set downward-closed subsets.
%% · Notice that the join operator has to be a _truncated_ \Sigma.
\begin{frame}{Locales of downward-closed subsets}
  Given a poset 
  \begin{align*}
    A &\quad:\quad \univ{}_m\\
    \sqsubseteq &\quad:\quad A \rightarrow A \rightarrow \mathsf{hProp}_m
  \end{align*}
  the type of \alert{downward-closed subsets} of $A$ is:
  \[ \sigmaty{U}{\pow{A}}{\pity{x~y}{A}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}} \]
  \begin{center}
    where
  \end{center}
  \begin{align*}
    &\mathcal{P} : \univ{}_m \rightarrow \univ{}_{m+1}\\
    &\mathcal{P}(A) \is A \rightarrow \mathsf{hProp}_m
  \end{align*}
\end{frame}

\begin{frame}
  This forms a \alert{frame}:
  \begin{align*}
    \top                      &\quad\is{}\quad \lambda \_.~ \mathsf{1}\\
    A \wedge B                  &\quad\is{}\quad \lambda x.~ (x \in A) \times (x \in B)\\
    \bigvee_{i~:~I} \mathbf{B}_i &\quad\is{}\quad \lambda x.~ \trunc{\sigmaty{i}{I}{x \in \mathbf{B}_i}}
  \end{align*}
\end{frame}

%% Slide 3.
%% · What is a nucleus? As you can see, it is just a monad on a poset, meaning it is a
%%   certain modality, and it is an idea going back to Tarski that topologies are models
%%   of modal logic, so we are really looking for the topological structure on this poset.
\begin{frame}{Nuclei for frames}
  Question: can we get all frames out of posets in this way?

  \vspace{1em}

  One way is to employ the notion of a \alert{nucleus}.

  \vspace{1em}

  Let $F$ be a frame. A \alert{nucleus} on $F$ is an endofunction $\mathbf{j} : \abs{F} \rightarrow
  \abs{F}$ such that
  \begin{align}
    &\pity{x~~}{A}{x \sqsubseteq \bj(x)} && [\text{extensiveness}],\\
    &\pity{x~y}{A}{\bj(x \wedge y) = \bj(x) \wedge \bj(y)} && [\text{meet preservation}], \text{and}\\
    &\pity{x~~}{A}{\bj(\bj(x)) \sqsubseteq \bj(x)} && [\text{idempotence}].
  \end{align}
\end{frame}

%% Slide 4.
%% · We have a problem: the codomain is not hProp? Can we make it so?
%%     Option: truncate. Not going to work.
%%     Solution: truncate _from the inside_ so we can have both.
\begin{frame}{Closure operators}
  In the particular case where $F$ is the locale of downward-closed subsets for a poset $A
  : \univ{}_m$, the nucleus can be seen as a \alert{closure operator}---\textbf{if it can
  be shown to be propositional}.

  \begin{align*}
    \only<3>{
    \RHD \quad&:\quad \underbrace{\pow{A} \rightarrow A \rightarrow \univ{}_{m}}_\text{\alert{This is what we have.}}\\
    }
    \only<2>{
    \RHD \quad&:\quad \underbrace{\pow{A} \rightarrow A \rightarrow \mathsf{hProp}_{m}}_\text{\alert{This is what we want.}}
    }
    \only<1>{
      \RHD \quad&:\quad \underbrace{\pow{A} \rightarrow \pow{A}}_\text{\alert{This is what we want.}}
    }
  \end{align*}
\end{frame}

%% Slide 5.1.
\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  \begin{code}[hide]
  {-# OPTIONS --cubical #-}

  open import Data.Nat using (ℕ)
  open import Cubical.Core.Everything
  open import Cubical.Foundations.Prelude using (isProp)
  open import Data.Product using (_×_; _,_)
  open import Function using (flip)
  \end{code}
  \begin{code}
  data 𝔻  : Type₀ where
    []    : 𝔻
    _⌢_   : 𝔻 → ℕ → 𝔻

  IsDC : (𝔻 → Type₀) → Type₀
  IsDC P = (σ : 𝔻) (n : ℕ) → P σ → P (σ ⌢ n)

  \end{code}
\end{frame}

%% Slide 5.2.
\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  \only<1-2>{
  \begin{code}
  data _◀_ (σ : 𝔻) (P : 𝔻 → Type₀) : Type₀ where
    dir      : P σ → σ ◀ P
    branch   : ((n : ℕ) → (σ ⌢ n) ◀ P) → σ ◀ P
    squash   : (φ ψ : σ ◀ P) → φ ≡ ψ
  \end{code}
  We can now show that this defines a nucleus, without choice!
  }

  \only<2>{
  Using the following, and then \emph{truncating from the outside} does not work.
  \begin{code}
  data _◃_ (σ : 𝔻) (P : 𝔻 → Type₀) : Type₀ where
    dir      : P σ → σ ◃ P
    branch   : ((n : ℕ) → (σ ⌢ n) ◃ P) → σ ◃ P
  \end{code}
    }

  \begin{code}[hide]
  variable
    m n : ℕ; σ τ : 𝔻; P Q : 𝔻 → Type₀

  ◀-prop : isProp (σ ◀ P)
  ◀-prop = squash
  \end{code}
\end{frame}

%% Slide 5.2.
\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  We can now prove the following idempotence law, without using countable choice
  ($\pity{i}{I}{\|  B_i \|} \rightarrow \| \pity{i}{I}{B_i} \|$).
  \begin{code}
  δ : σ ◀ P → ((v : 𝔻) → P v → v ◀ Q) → σ ◀ Q
  δ (dir     uεP)          φ  = φ _ uεP
  δ (branch  f)            φ  = branch (λ n →  δ (f n) φ)
  δ (squash  u◀P₀ u◀P₁ i)  φ  = squash (δ u◀P₀ φ) (δ u◀P₁ φ) i

  idempotence : σ ◀ (λ - → - ◀ P) → σ ◀ P
  idempotence u◀◀P = δ u◀◀P (λ _ v◀P → v◀P)
  \end{code}
\end{frame}

\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  \begin{code}
  -- ζ inference à la Brouwer.
  ζ : (n : ℕ) → IsDC P → σ ◀ P → (σ ⌢ n) ◀ P
  ζ n dc (dir     σεP)         = dir (dc _ n σεP)
  ζ n dc (branch  f)           = branch λ m → ζ m dc (f n)
  ζ n dc (squash  σ◀P σ◀P′ i)  = squash (ζ n dc σ◀P) (ζ n dc σ◀P′) i

  ζ′ : IsDC P → IsDC (λ - → - ◀ P)
  ζ′ P-dc σ n σ◀P = ζ n P-dc σ◀P
  \end{code}
\end{frame}

\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  \begin{code}
  lemma : IsDC P → P σ → σ ◀ Q → σ ◀ (λ - → P - × Q -)
  lemma dc σεP (dir σεQ)           = dir (σεP , σεQ)
  lemma dc σεP (branch f)          = branch (λ n → lemma dc (dc _ n σεP) (f n))
  lemma dc σεP (squash σ◀Q σ◀Q′ i) = squash (lemma dc σεP σ◀Q) (lemma dc σεP σ◀Q′) i

  mp : IsDC P → IsDC Q → σ ◀ P → σ ◀ Q → σ ◀ (λ - → P - × Q -)
  mp P-dc Q-dc (dir    σεP)        σ◀Q = lemma P-dc σεP σ◀Q
  mp P-dc Q-dc (branch f)          σ◀Q = branch (λ n → mp P-dc Q-dc (f n) (ζ n Q-dc σ◀Q))
  mp P-dc Q-dc (squash σ◀P σ◀P′ i) σ◀Q = squash (mp P-dc Q-dc σ◀P σ◀Q) (mp P-dc Q-dc σ◀P′ σ◀Q) i
  \end{code}
\end{frame}


%% Slide 5.3.
\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  This example can be accessed at:
  \begin{center}
    \url{https://ayberkt.gitlab.io/msc-thesis/BaireSpace.html}
  \end{center}
\end{frame}

\end{document}
