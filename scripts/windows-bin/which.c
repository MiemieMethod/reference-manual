#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <io.h>

static int has_sep(const char *s) {
  return strchr(s, '/') || strchr(s, '\\');
}

static int exists_file(const char *path) {
  return _access(path, 0) == 0;
}

static void print_path(const char *path) {
  for (const char *p = path; *p; ++p) {
    putchar(*p == '/' ? '\\' : *p);
  }
  putchar('\n');
}

static int try_candidate(const char *dir, const char *name) {
  char path[8192];
  if (dir && *dir) {
    snprintf(path, sizeof(path), "%s\\%s", dir, name);
  } else {
    snprintf(path, sizeof(path), "%s", name);
  }
  if (exists_file(path)) {
    print_path(path);
    return 1;
  }
  if (!strchr(name, '.')) {
    snprintf(path, sizeof(path), "%s\\%s.exe", dir && *dir ? dir : ".", name);
    if (exists_file(path)) {
      print_path(path);
      return 1;
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) return 1;
  const char *name = argv[1];
  if (has_sep(name)) {
    if (exists_file(name)) {
      print_path(name);
      return 0;
    }
    return 1;
  }

  char *path = getenv("PATH");
  if (!path) return 1;
  char *copy = _strdup(path);
  if (!copy) return 1;

  int found = 0;
  char *ctx = NULL;
  for (char *dir = strtok_s(copy, ";", &ctx); dir; dir = strtok_s(NULL, ";", &ctx)) {
    if (try_candidate(dir, name)) {
      found = 1;
      break;
    }
  }
  free(copy);
  return found ? 0 : 1;
}
