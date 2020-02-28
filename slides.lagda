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
\author{\textbf{Ayberk Tosun} and Thierry Coquand (Supervisor)}
\institute{Chalmers University of Technology}

\begin{document}

\maketitle

\begin{frame}{Motivation}
  \begin{align*}
    \text{{\huge Top}}&\text{{\huge ology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{constructively}} \\
    \text{{\huge Pointles}}&\text{{\huge s~topology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{predicatively}} \\
    \text{{\huge Forma}}&\text{{\huge l~topology}}\\
  \end{align*}
\end{frame}

\begin{frame}{What locales are like}
  \begin{itemize}
    \item<1-> Abstraction of open sets of a topology.
    \item<1-> Logic of \emph{observable properties}.
    \item<1-> CS view: logic of \emph{semidecidable properties}.
    \item<2> ``Junior-grade topos theory''.
  \end{itemize}
\end{frame}

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

\begin{frame}{Locales of downward-closed subsets}
  Given a poset
  \begin{align*}
    A &\quad:\quad \univ{}_m\\
    \sqsubseteq &\quad:\quad A \rightarrow A \rightarrow \mathsf{hProp}_m
  \end{align*}
  the type of \alert{downward-closed subsets} of $A$ is:
  \[ \sigmaty{U}{\pow{A}}{\pity{x~y}{A}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}}, \]
  \begin{center}
    where
  \end{center}
  \begin{align*}
    &\mathcal{P} : \univ{}_m \rightarrow \univ{}_{m+1}\\
    &\mathcal{P}(A) \is A \rightarrow \mathsf{hProp}_m.
  \end{align*}
\end{frame}

\begin{frame}
  This forms a \alert{locale}:
  \begin{align*}
    \top                      &\quad\is{}\quad \lambda \_.~ \mathsf{1}\\
    A \wedge B                  &\quad\is{}\quad \lambda x.~ (x \in A) \times (x \in B)\\
    \bigvee_{i~:~I} \mathbf{B}_i &\quad\is{}\quad \lambda x.~ \trunc{\sigmaty{i}{I}{x \in \mathbf{B}_i}}
  \end{align*}
\end{frame}

\begin{frame}{Nuclei for locales}
  Question: can we get all locales out of posets in this way?

  \vspace{1em}

  One way is to employ the notion of a \alert{nucleus}.

  \vspace{1em}

  Let $F$ be a locale. A \alert{nucleus} on $F$ is an endofunction $\mathbf{j} : \abs{F} \rightarrow
  \abs{F}$ such that
  \begin{align}
    &\pity{x~~}{A}{x \sqsubseteq \bj(x)} && [\text{extensiveness}],\\
    &\pity{x~y}{A}{\bj(x \wedge y) = \bj(x) \wedge \bj(y)} && [\text{meet preservation}], \text{and}\\
    &\pity{x~~}{A}{\bj(\bj(x)) \sqsubseteq \bj(x)} && [\text{idempotence}].
  \end{align}
\end{frame}

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

\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  \only<1>{
  \begin{code}
  data _◀_ (σ : 𝔻) (P : 𝔻 → Type₀) : Type₀ where
    dir      : P σ → σ ◀ P
    branch   : ((n : ℕ) → (σ ⌢ n) ◀ P) → σ ◀ P
    squash   : (p q : σ ◀ P) → p ≡ q
  \end{code}
  We can now show that this defines a nucleus, without choice!
  }

  \only<2>{
  Using the following, and then \emph{truncating from the outside} does not work.
  \begin{code}
  data _◀⋆_ (σ : 𝔻) (P : 𝔻 → Type₀) : Type₀ where
    dir      : P σ → σ ◀⋆ P
    branch   : ((n : ℕ) → (σ ⌢ n) ◀⋆ P) → σ ◀⋆ P
    -- squash : (φ ψ : σ ◀ P) → φ ≡ ψ
  \end{code}
    }

  \begin{code}[hide]
  variable
    m n : ℕ; σ τ : 𝔻; P Q : 𝔻 → Type₀

  ◀-prop : isProp (σ ◀ P)
  ◀-prop = squash
  \end{code}
\end{frame}

\begin{frame}{Baire space ($\mathbb{N} \rightarrow \mathbb{N}$)}
  We can now prove the following idempotence law, without using countable choice
  ($\pity{i}{I}{\|  B_i \|} \rightarrow \| \pity{i}{I}{B_i} \|$).
  \begin{code}
  δ : σ ◀ P → ((v : 𝔻) → P v → v ◀ Q) → σ ◀ Q
  δ (dir     uεP)          φ  = φ _ uεP
  δ (branch  f)            φ  = branch (λ n →  δ (f n) φ) --> problem
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
  This example can be accessed at:
  \begin{center}
    \url{https://ayberkt.gitlab.io/msc-thesis/BaireSpace.html}
  \end{center}
\end{frame}

\end{document}
