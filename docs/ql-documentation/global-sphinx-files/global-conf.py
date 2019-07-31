# -*- coding: utf-8 -*-
#
# Global configuration file, created on 29th April 2019.
#
# The config values below are used across all of the sphinx projects
# 
# Note that not all possible configuration values are present in this file.
#
# All configuration values have a default; values that are commented out
# serve to show the default.

# For details of all possible config values, 
# see https://www.sphinx-doc.org/en/master/usage/configuration.html

##################################################################################
#
# Project-specific values are configured in the relevant conf.py file. 
# See individual projects for details 
#
##################################################################################

# -- GLOBAL GENERAL CONFIG VALUES ------------------------------------------------

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
# source_suffix = ['.rst', '.md']
source_suffix = '.rst'

# If your documentation needs a minimal Sphinx version, state it here.
#needs_sphinx = '1.0'

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    'sphinx.ext.intersphinx',
    'sphinx.ext.mathjax',
]

# The encoding of source files.
#source_encoding = 'utf-8-sig'

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# Import the QL Lexer to use for syntax highlighting
import sys

def setup(sphinx):
    sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), os.path.pardir, 'global-sphinx-files')))
    from qllexer import QLLexer
    sphinx.add_lexer("ql", QLLexer())

# The Semmle version info for the current release you're documenting, acts as replacement for
# |version| and |release|, also used in various other places throughout the
# built documents.
#
# The short X.Y version.
version = u'1.21'
# The full version, including alpha/beta/rc tags.
release = u'1.21'
copyright = u'2019 Semmle Ltd'
author = u'Semmle Ltd'

# The language for content autogenerated by Sphinx. Refer to documentation
# for a list of supported languages.
language = None

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = False

# If true, links to the reST sources are added to the pages.
html_show_sourcelink = False

# If true, "Created using Sphinx" is shown in the HTML footer. Default is True.
html_show_sphinx = False

# -- Global HTML configuration -------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
html_theme = 'alabaster'

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
html_theme_options = {'font_size': '16px',
                      'body_text': '#333', 
                      'link': '#2F1695',
                      'link_hover': '#2F1695',
                      'font_family': 'Lato, sans-serif',
                      'head_font_family': 'Moderat, sans-serif',
                      'show_powered_by': False,
                      'nosidebar':True,
                      }

# Add any paths that contain templates here, relative to this directory.
templates_path = ['../global-sphinx-files/_templates']

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['../global-sphinx-files/_static']

intersphinx_mapping = {}

##############################################################################