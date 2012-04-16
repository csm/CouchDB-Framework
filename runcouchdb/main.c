//
//  main.c
//  runcouchdb
//
//  Created by Casey Marshall on 4/15/12.
//  Copyright (c) 2012 Memeo, Inc. All rights reserved.
//
// This is a "port" of the shell script launcher 'couchdb' from
// Apache CouchDB. It exists because parsing command line arguments
// in shell scripts won't work in all cases.
//
// This is meant to run on Mac OS X only.

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <stdarg.h>
#include <limits.h>
#include <libgen.h>
#include <getopt.h>
#include <signal.h>
#include <fcntl.h>
#include <dirent.h>
#include <sys/stat.h>

static int
readpid(char *path)
{
    int pid;
    FILE *f = fopen(path, "r");
    if (f == NULL)
        return -1;
    if (fscanf(f, "%d", &pid) != 1)
    {
        fclose(f);
        return -1;
    }
    return pid;
}

char *
pathappend(char *s, const char *ss)
{
    char *ret = malloc(strlen(s) + strlen(ss) + 2);
    if (s == NULL)
        return NULL;
    ret[0] = '\0';
    strcat(ret, s);
    strcat(ret, "/");
    strcat(ret, ss);
    return ret;
}

static void display_version(char *progname)
{
    printf("%s %s", basename(progname), " - Apache CouchDB 1.2.0\n"
           "\n"
           "Licensed under the Apache License, Version 2.0 (the \"License\"); you may not use\n"
           "this file except in compliance with the License. You may obtain a copy of the\n"
           "License at\n"
           "\n"
           "http://www.apache.org/licenses/LICENSE-2.0\n"
           "\n"
           "Unless required by applicable law or agreed to in writing, software distributed\n"
           "under the License is distributed on an \"AS IS\" BASIS, WITHOUT WARRANTIES OR\n"
           "CONDITIONS OF ANY KIND, either express or implied. See the License for the\n"
           "specific language governing permissions and limitations under the License.");

}

static void display_help(char *progname, char * const *erl_start_options)
{
    printf("Usage: %s [OPTION]\n"
           "\n"
           "The %s command runs the Apache CouchDB server.\n"
           "\n"
           "Erlang is called with:\n   ", progname, progname);
    int i = 0;
    while (erl_start_options[i] != NULL)
    {
        printf(" %s", erl_start_options[i]);
        i++;
    }
           //$ERL_START_OPTIONS
    printf("\n\n"
           "Erlang inherits the environment of this command.\n"
           "\n"
           "You can override these options using the environment:\n"
           "\n"
           "    ERL_AFLAGS, ERL_FLAGS, ERL_ZFLAGS\n"
           "\n"
           "See erl(1) for more information about the environment variables.\n"
           "\n"
           "The exit status is 0 for success or 1 for failure.\n"
           "\n"
           "Options:\n"
           "\n"
           "  -h          display a short help message and exit\n"
           "  -V          display version information and exit\n"
           "  -a FILE     add configuration FILE to chain\n"
           "  -A DIR      add configuration DIR to chain\n"
           "  -n          reset configuration file chain (including system default)\n"
           "  -c          print configuration file chain and exit\n"
           "  -i          use the interactive Erlang shell\n"
           "  -b          spawn as a background process\n"
           "  -p FILE     set the background PID FILE (overrides system default)\n"
           "  -r SECONDS  respawn background process after SECONDS (defaults to no respawn)\n"
           "  -o FILE     redirect background stdout to FILE (defaults to $STDOUT_FILE)\n"
           "  -e FILE     redirect background stderr to FILE (defaults to $STDERR_FILE)\n"
           "  -s          display the status of the background process\n"
           "  -k          kill the background process, will respawn if needed\n"
           "  -d          shutdown the background process\n"
           "\n"
           "Report bugs at <https://issues.apache.org/jira/browse/COUCHDB>.\n");
}

static char **append_array(char **array, const char *str)
{
    int count = 0;
    if (array != NULL)
    {
        while (array[count] != NULL) count++;
    }
    array = realloc(array, (count + 2) * sizeof(char *));
    array[count] = strdup(str);
    array[count+1] = NULL;
    return array;
}

static char **concat_arrays(char **array, char **array2)
{
    int i = 0;
    while (array2[i] != NULL)
    {
        array = append_array(array, array2[i]);
        i++;
    }
    return array;
}

static char **append_config_dir(char **paths, const char *dir)
{
    DIR *d = opendir(dir);
    struct dirent *ent;
    if (d == NULL)
    {
        perror(dir);
        return paths;
    }
    while ((ent = readdir(d)) != NULL)
    {
        size_t len = strlen(ent->d_name);
        if (len < 4)
            continue;
        if (strcmp(".ini", ent->d_name + len - 4) == 0)
        {
            paths = append_array(paths, ent->d_name);
        }
    }
    return paths;
}

int mkdirs(const char *path)
{
    struct stat st;
    if (stat(path, &st) == 0 && S_ISDIR(st.st_mode))
        return 0;
    char *parent = strdup(dirname(path));
    if (mkdirs(parent) != 0)
    {
        free(parent);
        return -1;
    }
    free(parent);
    return mkdir(path, 0777);
}

int main(int argc, const char * argv[], const char *env[], const char *path[])
{
    char *dir = strdup(dirname((char *) path[0]));
    dir = realloc(dir, strlen(dir) + 4);
    strcat(dir, "/..");
    char *home = realpath(dir, NULL);
    char *bindir = pathappend(home, "bin");
    char *localconfdir = pathappend(home, "etc/couchdb");
    char *locallibdir = pathappend(home, "lib");
    char *localerlanglibdir = pathappend(locallibdir, "couchdb/erlang/lib");
    char *localstatedir = pathappend(getenv("HOME"), "Library/Application Support/CouchDB");
    int background = 0;
    char *default_config_dir = pathappend(localconfdir, "default.d");
    char *default_config_file = pathappend(localconfdir, "default.ini");
    const char *erl_start_options[] = {
        "-os_mon",
        "start_memsup", "false",
        "start_cpu_sup", "false",
        "disk_space_check_interval", "1",
        "disk_almost_full_threshold", "1",
        "-sasl", "errlog_type", "error", "+K", "true", "+A", "4",
        NULL
    };
    char *erl = pathappend(bindir, "erl");
    int heart_beat_timeout = 11;
    char *heart_command = pathappend(bindir, "couchdb -k");
    int interactive = 0;
    int _kill = 0;
    const char *local_config_dir = pathappend(localconfdir, "local.d");
    const char *local_config_file = pathappend(localconfdir, "local.ini");
    const char *pid_file = pathappend(localstatedir, "run/couchdb/couchdb.pid");
    int recursed = 0;
    int reset_config = 1;
    int respawn_timeout = 0;
    int script_error = 1;
    int script_ok = 0;
    int shutdown = 0;
    const char *stderr_file = "couchdb.stderr";
    const char *stdout_file = "couchdb.stdout";

    char **config_files = NULL;
    config_files = append_config_dir(config_files, default_config_dir);
    config_files = append_array(config_files, default_config_file);
    config_files = append_config_dir(config_files, local_config_dir);
    config_files = append_array(config_files, local_config_file);
    int ch;
    const char *optstring = "hVa:A:ncibp:r:Ro:e:skd";
    while ((ch = getopt(argc, argv, optstring)) != -1)
    {
        switch (ch)
        {
            case 'h':
                display_help(argv[0], erl_start_options);
                exit(0);
                
            case 'V':
                display_version(argv[0]);
                exit(0);
                
            case 'a':
                config_files = append_array(config_files, optarg);
                break;
                
            case 'A':
                config_files = append_config_dir(config_files, optarg);
                break;
                
            case 'n':
                break; // TODO
                
            case 'c':
                break; // TODO
                
            case 'i':
                interactive = 1;
                break;
                
            case 'b':
                background = 1;
                break;
                
            case 'r':
                respawn_timeout = atoi(optarg);
                break;
                
            case 'R':
                recursed = 1;
                break;
                
            case 'p':
                pid_file = optarg;
                break;
                
            case 'o':
                stdout_file = optarg;
                break;
                
            case 'e':
                stderr_file = optarg;
                break;
                
            case 's':
                break; //TODO
                
            case 'k':
                _kill = 1;
                break;
                
            case 'd':
                shutdown = 1;
                break;
                
            default:
                fprintf(stderr, "Try `%s -h' for more information.\n", argv[0]);
                exit(1);
        }
    }
    
#if DEBUG
    printf("bindir: %s\nerl: %s\nlocalconfdir: %s\nlocalerlanglibdir: %s\nlocallibdir: %s\nlocalstatedir: %s\n", bindir, erl, localconfdir, localerlanglibdir, locallibdir, localstatedir);
#endif
    
    if (_kill || shutdown)
    {
        int pid = readpid(pid_file);
        if (_kill)
            fclose(fopen(pid_file, "w"));
        if (pid > 0)
        {
            if (kill(pid, 0) == 0)
            {
                if (kill(pid, SIGHUP) == 0)
                {
                    printf("Apache CouchDB has been %s\n", _kill ? "killed" : "shutdown");
                }
                else
                {
                    printf("Apache CouchDB could not be killed");
                }
            }
            else
            {
                printf("Apache CouchDB is not running.");
            }
        }
    }
    else
    {
        const char *interactive_options[] = { "+Bd", "-noinput", NULL };
        if (interactive && !background)
            interactive_options[0] = NULL;
        if (background)
        {
            pid_t child = fork();
            if (child < 0)
            {
                perror("error forking");
                exit(1);
            }
            if (child > 0)
            {
                char *dir = strdup(dirname(pid_file));
                mkdirs(dir);
                FILE *f = fopen(pid_file, "w");
                fprintf(f, "%d\n", child);
                fclose(f);
                
                int wait = 4;
                while (wait > 0)
                {
                    if (kill(child, 0) != 0)
                    {
                        fprintf(stderr, "Failed to launch CouchDB.\n");
                        exit(1);
                    }
                    usleep(250000);
                    wait--;
                }
                printf("Apache CouchDB has started, time to relax.\n");
                exit(0);
            }
        }
        
        char **prog_arguments = NULL;
        prog_arguments = append_array(prog_arguments, erl);
        prog_arguments = concat_arrays(prog_arguments, interactive_options);
        prog_arguments = concat_arrays(prog_arguments, erl_start_options);
        prog_arguments = append_array(prog_arguments, "-env");
        prog_arguments = append_array(prog_arguments, "ERL_LIBS");
        prog_arguments = append_array(prog_arguments, localerlanglibdir);
        prog_arguments = append_array(prog_arguments, "-couch_ini");
        prog_arguments = concat_arrays(prog_arguments, config_files);
        prog_arguments = append_array(prog_arguments, "-s");
        prog_arguments = append_array(prog_arguments, "couch");
        
        if (background)
        {
            fflush(stdout);
            int newout = open(stdout_file, O_CREAT|O_WRONLY);
            int oldout = dup(fileno(stdout));
            dup2(newout, oldout);
            close(newout);
            close(oldout);
            fflush(stderr);
            int newerr = open(stderr_file, O_CREAT|O_WRONLY);
            int olderr = dup(fileno(stderr));
            dup2(newerr, olderr);
            close(newerr);
            close(olderr);
        }
        
#if DEBUG
        printf("execve(%s, {", erl);
        {
            int __x = 0;
            while (prog_arguments[__x] != NULL)
            {
                printf("%s%s", prog_arguments[__x], prog_arguments[__x+1] == NULL ? "" : ", ");
                __x++;
            }
            printf("}, env...);\n");
        }
#endif
        
        execve(erl, prog_arguments, env);
    }
    
    return 0;
}

