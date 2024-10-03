#pragma once

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef enum SolverResult {
  Sat,
  Unsat,
  Unknown,
} SolverResult;

typedef struct SmithrilSort {
  const void *_0;
} SmithrilSort;

typedef struct SmithrilContext {
  const void *_0;
} SmithrilContext;

typedef struct SmithrilTerm {
  const void *_0;
} SmithrilTerm;

typedef struct SmithrilOptions {
  const void *_0;
} SmithrilOptions;

typedef struct SmithrilSolver {
  const void *_0;
} SmithrilSolver;

typedef struct SmithrilTermVector {
  const void *_0;
} SmithrilTermVector;

struct SmithrilSort smithril_mk_bv_sort(struct SmithrilContext context, uint64_t size);

struct SmithrilSort smithril_mk_array_sort(struct SmithrilContext context,
                                           struct SmithrilSort index_sort,
                                           struct SmithrilSort elem_sort);

struct SmithrilSort smithril_mk_bool_sort(struct SmithrilContext context);

struct SmithrilTerm smithril_mk_bv_value_uint64(struct SmithrilContext context,
                                                struct SmithrilSort sort,
                                                uint64_t val);

struct SmithrilTerm smithril_mk_smt_symbol(struct SmithrilContext context,
                                           const char *name,
                                           struct SmithrilSort sort);

struct SmithrilTerm smithril_mk_and(struct SmithrilContext context,
                                    struct SmithrilTerm term1,
                                    struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvadd(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_or(struct SmithrilContext context,
                                   struct SmithrilTerm term1,
                                   struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_eq(struct SmithrilContext context,
                                   struct SmithrilTerm term1,
                                   struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_implies(struct SmithrilContext context,
                                        struct SmithrilTerm term1,
                                        struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_neq(struct SmithrilContext context,
                                    struct SmithrilTerm term1,
                                    struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_xor(struct SmithrilContext context,
                                    struct SmithrilTerm term1,
                                    struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvand(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvashr(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvlshr(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvmul(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvnand(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvneg(struct SmithrilContext context, struct SmithrilTerm term1);

struct SmithrilTerm smithril_mk_bvnor(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvnot(struct SmithrilContext context, struct SmithrilTerm term1);

struct SmithrilTerm smithril_mk_bvnxor(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvor(struct SmithrilContext context,
                                     struct SmithrilTerm term1,
                                     struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsdiv(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsge(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsgt(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvshl(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsle(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvslt(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsmod(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvsub(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvudiv(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvuge(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvugt(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvule(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvult(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvumod(struct SmithrilContext context,
                                       struct SmithrilTerm term1,
                                       struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_bvxor(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2);

struct SmithrilTerm smithril_mk_not(struct SmithrilContext context, struct SmithrilTerm term1);

struct SmithrilTerm smithril_mk_store(struct SmithrilContext context,
                                      struct SmithrilTerm term1,
                                      struct SmithrilTerm term2,
                                      struct SmithrilTerm term3);

struct SmithrilOptions smithril_new_options(void);

struct SmithrilContext smithril_new_context(void);

struct SmithrilSolver smithril_new_solver(struct SmithrilContext context);

enum SolverResult smithril_check_sat(struct SmithrilSolver solver);

void smithril_reset(struct SmithrilSolver solver);

void smithril_push(struct SmithrilSolver solver);

void smithril_pop(struct SmithrilSolver solver);

void smithril_assert(struct SmithrilSolver solver, struct SmithrilTerm term);

const char *smithril_eval(struct SmithrilSolver solver, struct SmithrilTerm term);

struct SmithrilTermVector smithril_unsat_core(struct SmithrilSolver solver);

uint64_t smithril_unsat_core_size(struct SmithrilTermVector unsat_core);

struct SmithrilTerm smithril_unsat_core_get(struct SmithrilContext context,
                                            struct SmithrilTermVector unsat_core,
                                            uint64_t index);

void smithril_delete_options(struct SmithrilOptions options);

void smithril_set_timeout(struct SmithrilOptions options, const char *timeout);

void smithril_set_produce_unsat_core(struct SmithrilOptions options, bool val);

void smithril_delete_context(struct SmithrilContext context);

void smithril_delete_solver(struct SmithrilSolver solver);
