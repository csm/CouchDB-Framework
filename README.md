This repo is for building an embeddable framework out of CouchDB for Mac OS X.

The biggest problem with CouchDB and Erlang is their dependence on an "installation directory" to find the system paths, since the `couchdb` and `erl` programs are really just scripts that have the real paths embedded as hard-coded for-that-installation strings.

The changes here should make it possible to place this framework anywhere on the disk, even embedded in your application, and you can run CouchDB from inside that 

Notes:

1. You should use a custom config file to specify paths. In particular:
    * `[query_servers] javascript` and `coffeescript` -- you need to specify *where the framework is located* and the paths to these support files in your framework.
    * `[couchdb] database_dir`, `view_index_dir` -- you should specify a location for these either in some shared system directory, or in the user's home directory (e.g., under `${HOME}/Library/Application Support/Your App`).
    * `[couchdb] util_driver_dir` -- needs to be set to the location within your framework's install path, as above.
    * `[log] file` -- set this to some system logs directory, or a user logs directory (e.g. `${HOME}/Library/Logs/Your App/couch.log`).
    
2. The `couchdb` launcher script is not compatible with arguments that have spaces in them; the `runcouchdb` program does *almost* the same thing as the `couchdb` script, but since it is not a bash script it can handle arguments with spaces in them.

## TODO

* Prune the built erlang runtime of things not needed for running CouchDB.

* Verify 