\documentclass{beamer}
\usetheme{metropolis}
\usepackage{wasysym}
\usepackage{ebproof}

\newcommand{\pity}[3]{\prod_{(#1~:~#2)} #3}
\newcommand{\sigmaty}[3]{\sum_{(#1~:~#2)} #3}
\newcommand{\univ}{\mathcal{U}}
\newcommand{\rulename}[1]{\textsf{\color{blue} #1}}
\newcommand{\pow}[1]{\mathcal{P}\left( #1 \right)}
\newcommand{\trunc}[1]{\left\| #1 \right\|}
\newcommand{\abs}[1]{\left| #1 \right|}
\newcommand{\is}{:\equiv}

\setmonofont{PragmataPro Mono Liga}
\usepackage{agda}

\title{Pointless Topology in Univalent Foundations}

\date{\today}
\author{Ayberk Tosun}
\institute{Chalmers University of Technology}

\begin{document}

\maketitle

%% Slide 1.
\begin{frame}{Motivation}
  \begin{align*}
    \text{{\huge Top}}&\text{{\huge ology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{constructively}} \\
    \text{{\huge Pointles}}&\text{{\huge s~topology}}\\
    \text{\alert{understood}} &~\text{\huge $\Downarrow$}~\text{\alert{predicatively}} \\
    \text{{\huge Forma}}&\text{{\huge l~topology}}\\
  \end{align*}
\end{frame}

\begin{frame}{What frames are like}
  \begin{enumerate}
    \item<1-> Abstraction of open sets of a topology.
    \item<1-> Logic of ``observable properties'' (Vickers),
      ``affirmable properties'' (Abramsky).
    \item<1-> CS view: System of ``semidecidable properties'' (Smyth, Escard\'{o}), and
    \item<2> ``Junior-grade topos theory'' (Abramsky).
  \end{enumerate}
\end{frame}

%% Slide 1.
\begin{frame}{Frames}
  A poset $\mathcal{O}$ such that
  \begin{itemize}
    \item \alert{finite subsets} of $\mathcal{O}$ have \alert{meets},
    \item \alert{all subsets} of $\mathcal{O}$ have \alert{joins}, and
    \item binary meets distribute over arbitrary joins:
      \begin{equation*}
        A \wedge \left( \bigvee_{i~:~I} \mathbf{B}_i \right) = \bigvee_{i~:~I} \left( A \wedge \mathbf{B}_i \right),
      \end{equation*}
      for any $A \in \mathcal{O}$ and $I$-indexed family $\mathbf{B}$ over $\mathcal{O}$.
  \end{itemize}
\end{frame}

%% Slide 2.
\begin{frame}[fragile]{Example of a Frame}
  Given a poset $(A , \sqsubseteq)$, the type of \alert{downward-closed subsets} of $A$ is:
  \begin{equation*}
    \sigmaty{U}{\pow{A}}{\pity{x~y}{A}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}}.
  \end{equation*}

  This forms a \alert{frame}:
  \begin{align*}
    \top                      &\quad\is{}\quad triv\\
    A \wedge B                  &\quad\is{}\quad A \cap B\\
    \bigvee_{i~:~I} \mathbf{B}_i &\quad\is{}\quad \lambda x.~ \trunc{\sigmaty{i}{I}{x \in \mathbf{B}_i}}
  \end{align*}
\end{frame}

%% Slide 3.
\begin{frame}{Nuclei of Frames}
  Question: can we get all frames out of posets in this way?\\

  \vspace{1em}

  One way is to use a technical notion called a \alert{nucleus}.

  \vspace{1em}

  Let $F$ be a frame. A nucleus on $F$ is an endofunction $\mathbf{j} : \abs{F} \rightarrow \abs{F}$
  such that
  \begin{enumerate}
    \item $\pity{x}{A}{x \sqsubseteq \mathbf{j}(x)}$ (extensiveness),
    \item $\mathbf{j}(x \wedge y) = \mathbf{j}(x) \wedge \mathbf{j}(y)$, and
    \item $\mathbf{j}(\mathbf{j}(x)) = \mathbf{j}(x)$ (idempotence).
  \end{enumerate}

  \vspace{1em}

  \textbf{The set of fixed points of a nucleus on a frame forms a frame.}
\end{frame}

%% Slide 4.
\begin{frame}{Closure operators}
  Given a poset
  \begin{align*}
    A &\quad:\quad \univ{}_m\\
    \sqsubseteq &\quad:\quad A \rightarrow A \rightarrow \mathsf{hProp}_n
  \end{align*}
  we want a \alert{closure operator} on it.

  \vspace{1em}

  This is just a \alert{nucleus} on the frame of downward-closed subsets, which is the
  natural inductively defined \alert{coverage} relation.
  \begin{align*}
    \only<1>{
    \RHD \quad&:\quad \pow{A} \rightarrow A \rightarrow \univ{}_{m+1}
    }
    \only<2>{
    \RHD \quad&:\quad \underbrace{\pow{A} \rightarrow A \rightarrow \mathsf{hProp}_{m+1}}_\text{\alert{Can we achieve this?}}
    }
    \only<3>{
      \RHD \quad&:\quad \underbrace{\pow{A} \rightarrow \pow{A}}_\text{\alert{Can we achieve this?}}
    }
  \end{align*}

\end{frame}

%% Slide 5.
\begin{frame}{Baire space}
  \begin{code}[hide]
    {-# OPTIONS --cubical #-}

    open import Data.Nat using (ℕ)
    open import Cubical.Core.Everything
    open import Cubical.Foundations.Prelude using (isProp)
    open import Function using (flip)
  \end{code}
  \begin{code}
    data 𝔻 : Type₀ where
      nil   : 𝔻
      _∷<_  : 𝔻 → ℕ → 𝔻

    IsDC : (𝔻 → Type₀) → Type₀
    IsDC U = (σ : 𝔻) (n : ℕ) → U σ → U (σ ∷< n)

    data _◀_ (σ : 𝔻) (U : 𝔻 → Type₀) : Type₀ where
      dir      : U σ → σ ◀ U
      branch   : (n : ℕ) → ((σ ∷< n) ◀ U) → σ ◀ U
      squash   : (φ ψ : σ ◀ U) → φ ≡ ψ
  \end{code}
\end{frame}

\begin{frame}{Baire space}
  \begin{code}[hide]
    variable
      u v : 𝔻
      P Q : 𝔻 → Type₀
  \end{code}
  \begin{code}
    ◀-prop : isProp (u ◀ P)
    ◀-prop = squash

    δ : u ◀ P → ((v : 𝔻) → P v → v ◀ Q) → u ◀ Q
    δ (dir     uεP)          φ  = φ _ uεP
    δ (branch  n u◀P)        φ  = branch n (δ u◀P φ)
    δ (squash  u◀P₀ u◀P₁ i)  φ  = squash (δ u◀P₀ φ) (δ u◀P₁ φ) i

    prop₀-corollary : u ◀ (λ - → - ◀ P) → u ◀ P
    prop₀-corollary u◀◀P = δ u◀◀P (λ _ v◀P → v◀P)
  \end{code}
\end{frame}



\end{document}
