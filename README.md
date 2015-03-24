# SHARED RESOURCES IMPLEMENTATIONS 
(README in progress)

Several Implementations for the following shared resources:

* Semaphore
* Bounded Semaphore
* Readers-Writers*
* Observer - Event Manager

### What is this repository for?

* Examples of Shared resources specifications within its implementation

### General Code Conventions

* Use UTF-8
* Use 2 space indent, no tabs.
* Use Unix-style line endings. On the last line of the file, too.
* Use spaces around operators, after ,, : and ;, around { and before }.
* No spaces after (, [ and before ], ).
* Use an empty line before the return value of a method (unless it only has one line), and an empty line between defs.
* Use empty lines to break up a long method into logical paragraphs.
* Keep lines fewer than 80 characters.
* Avoid trailing whitespace.
* Java Source code suffixes
  * Sync: using synchronization
  * Monitor: using Babel Priority Monitors
  * JCSP: using third party JCSP library from Kent University
  * Spec or no suffix: Java interface with JML specification
  * Key: code instrumentalization for KeY Verification
* Java tester must follow suffixes policy and use preffix Test

### License

Copyright (c) 2014 Babel Group - UPM - Madrid
 
Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the 'Software'), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
