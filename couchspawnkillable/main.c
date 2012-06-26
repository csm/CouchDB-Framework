//
//  main.c
//  CouchDB
//
//  Created by Casey Marshall on 4/24/12.
//  Copyright (c) 2012 Memeo, Inc. All rights reserved.
//

#include <stdio.h>
#include <unistd.h>

int main(int argc, char **argv, char **envp)
{
    printf("kill -9 %d\n", getpid());
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    setvbuf(stdin, NULL, _IONBF, 0);
    execve(argv[1], argv+1, envp);
    return 1;
}