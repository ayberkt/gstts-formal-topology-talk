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

\title{Pointless Topology in Univalent Foundations}

\date{\today}
\author{Ayberk Tosun}
\institute{Chalmers University of Technology}

\begin{document}

\begin{code}
  module slides where
\end{code}

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
\end{frame}

%% Slide 5.
\begin{frame}{Baire space}
  \begin{code}
  \end{code}
\end{frame}

\end{document}
