\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{modjflart}[2024/10/29 almmost JFLA LaTeX class]

\LoadClass[10pt,a4paper]{scrartcl}

\RequirePackage[margin=1.4in]{geometry}

\RequirePackage[draft=false]{scrlayer-scrpage}

\RequirePackage{authblk} %% Manage authors list and affiliations

\RequirePackage{ifdraft} %% Draft and finals mode for submissions

% Mise en forme des légendes de figures
\RequirePackage[labelfont=bf, labelsep=period]{caption}

% Quelques paquets utiles pour toutes les soumissions
\RequirePackage{amsmath,amssymb} % symboles de math et notations
\RequirePackage{amsthm} % définition d'environnements de théorèmes
\RequirePackage{mathpartir} % édition de math
\RequirePackage[hidelinks]{hyperref} % handling references and links

\RequirePackage[mathlines]{lineno} %% Line numbers for submissions, including math lines

%\RequirePackage{cleveref}
% smart references -- must be loaded AFTER
% hyperref, currently unusable in conjunction with babel-french https://tex.stackexchange.com/a/83818

\RequirePackage[draft=false]{microtype} % pour positionner l'option draft à faux

\RequirePackage{color,graphicx}

\newif\ifjflart@english
\DeclareOption{english}{\jflart@englishtrue}

\ProcessOptions\relax

\ifjflart@english
  \RequirePackage[english]{babel}
\else
  \RequirePackage[french]{babel}
  % Overload author separator for authblk, avoiding the dreaded Oxford comma
  \renewcommand\Authand{ et }
  \renewcommand\Authands{ et }
\fi
\RequirePackage{iflang}

\theoremstyle{plain}
\newtheorem{theo}{\IfLanguageName{french}{Théorème}{Theorem}}
\newtheorem{prop}{\IfLanguageName{french}{Proposition}{Proposition}}
\newtheorem{conj}{\IfLanguageName{french}{Conjecture}{Conjecture}}
\newtheorem{coro}{\IfLanguageName{french}{Corollaire}{Corollary}}
\newtheorem{lemm}{\IfLanguageName{french}{Lemme}{Lemma}}
\theoremstyle{definition}
\newtheorem{defi}{\IfLanguageName{french}{Définition}{Definition}}
\theoremstyle{remark}
\newtheorem{remark}{\IfLanguageName{french}{Remarque}{Remark}}
\newtheorem{exem}{\IfLanguageName{french}{Exemple}{Example}}

% Pas de sans-serif dans les titre et sections
\setkomafont{sectioning}{\normalcolor\bfseries}
%% \setkomafont{title}{\normalfont\bfseries}

% Mode soumission : numéros de ligne
\setlength\linenumbersep{30pt}
\renewcommand\linenumberfont{\normalfont\footnotesize\color{red}}
\ifdraft{\linenumbers}{\nolinenumbers}

% Affiliations
\renewcommand{\Affilfont}{\small}

% Supprime les marqueurs d'affiliation dans la liste des auteurs.
%% https://tex.stackexchange.com/questions/126787/remove-affiliation-from-author
\newcommand{\authorlist}{{%
  \expandafter\let\csname textsuperscript \endcsname\@gobble% Remove \textsuperscript
  \AB@authlist}
}

% En-têtes, titre et liste d'auteurs courts
\newif\iftitlerunningundefined
\titlerunningundefinedtrue

\newif\ifauthorrunningundefined
\authorrunningundefinedtrue

\gdef\@titleRunning{\@title}
\gdef\@authorRunning{\authorlist}

\def\titlerunning#1
{
	\iftitlerunningundefined
		\gdef\@titleRunning{#1}
		\titlerunningundefinedfalse
	\else
		\ClassWarning{jflart}{Another use of titlerunning ignored}
	\fi
}

\def\authorrunning#1
{
	\ifauthorrunningundefined
		\gdef\@authorRunning{#1}
		\authorrunningundefinedfalse
	\else
		\ClassWarning{jflart}{Another use of authorrunning ignored}
	\fi
}

\makeatletter
\ihead{\small\@titleRunning}
\ohead{\small\@authorRunning}
\makeatother

% Pieds-de-page pour les JFLA (année et numéro d'édition)
\newif\ifjflaundefined
\jflaundefinedtrue

\gdef\jflaEds{34}
\gdef\jflaYear{2023}

\def\jfla#1#2{%
  \ifjflaundefined
     \gdef\jflaEds{#1}
     \gdef\jflaYear{#2}
     \jflaundefinedfalse
  \else
     \ClassError{jflart}{Edition and Year of JFLA paper or submission undefined}
  \fi
}

\cfoot*{}
\ifoot*{preprint}
% Mode final : pas de numéro de pages
\ofoot*{\ifoptionfinal{}{\small\pagemark}}

% Pas de date dans le titre
\date{}
