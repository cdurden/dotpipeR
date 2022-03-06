library(withr)
library(mockery)
envir <- new.env()
f <- function() {
    1
}
with_debug <- function(...) {
    with_options(list(dotpipeR.debug=TRUE),...)
}
exprs <- c(quote(a <- f()), quote(b <- a*2))
p <- pipeExprs(exprs, parent.env=envir)
q <- repipe(p, parent.env=envir)
r <- repipe(p, recalculate=c("a"), parent.env=envir)


test_that("pipe preprocessor setId works", {
  id <- "test-setId"
  #p <- with_debug(pipeExprs(exprs, parent=envir, processors=buildProcessors(prePipe=list(partial(setId,id=id)))))
  p <- pipeExprs(exprs, parent=envir, processors=buildProcessors(prePipe=list(partial(setId,id=id))))
  expect_equal(p$id, id)
})

testArgs <- list(recalculate="a",processors=buildProcessors())
lapply(names(testArgs), function(name) {
  test_that(paste0("pipe passes ",name," argument to buildCallGraph"), {
    args <- append(list(exprs=exprs, parent=envir),testArgs)
    m <- mock(length(exprs),cycle=TRUE) # FIXME: There should only be length(exprs) calls to buildCallGraph
    with_mock(buildCallGraph = m, {
      #with_debug(
        do.call(pipeExprs,args)
      #)
    })
    expect_equal(mock_args(m)[[1]][[name]], testArgs[[name]])
  })
})


test_that("pipe evaluates a simple expression", {
  expect_equal(p$vertices$b$value, 2)
})

test_that("default pipe processors match defaultProcessors()", {
  expect_equal(p$args$processors,defaultProcessors())
})

test_that("pipe processors can be cleared by passing initial=list()", {
  p <- pipeExprs(exprs, parent=envir, processors=buildProcessors(initial=list()))
  expect_length(unlist(p$args$processors),0)
})

test_that_processor_runs <- function(processorName) {
  test_that(paste0(processorName, " processor runs"), {
    makeTestProcessor <- function(msg) {
      function(x) {
        message(msg)
        x
      }
    }
    args <- list(initial=list())
    msg <- paste0("pipe ",processorName," processor ran")
    args[[processorName]] <- list(makeTestProcessor(msg))
    processors <- do.call(buildProcessors, args)
    expect_message(with_debug(pipeExprs(exprs, parent=envir, processors=processors)), msg)
  })
}

lapply(c("prePipe", "postPipe", "preEval", "postEval"), test_that_processor_runs)


test_that("pipeline vertices match assigned names", {
  expect_length(names(p$vertices), 2)
  expect_true(all(lapply(names(p$vertices), `%in%`, c("a","b"))))
})

test_that("pipeline edge names have the format a~b", {
  expect_equal(names(p$edges), vapply(p$edges, function(edge) paste(edge[[1]],edge[[2]],sep="~"), names(p$edges), USE.NAMES=FALSE))
})

test_that("pipeline edges connect inputs to outputs", {
  expect_length(names(p$edges), 1)
  expect_true(all(lapply(names(p$edges), `%in%`, c("a~b"))))
})

test_that("pipe saves vertex data", {
  expect_true(all(lapply(p$vertices, function(vertex) file.exists(vertexCacheFile(vertex)))))
})

test_that("pipeline has no cached values after the first run", {
  cachedValues <- lapply(p$vertices, `$`, "cache")
  expect_true(all(lapply(cachedValues, is.null)))
})

test_that("repipe retains pipeline id", {
  expect_equal(q$id, p$id)
})

test_that("pipeline vertices have cached data after repipe", {
  expect_true(all(lapply(q$vertices, function(vertex) { !is.null(vertex$cache) })))
})

test_that("pipeline values match the cache after repipe", {
  expect_true(all(lapply(q$vertices, function(vertex) { vertex$cache == vertex$value })))
})

test_that("repipe reevaluates specified vertices", {
  #expect_message(with_debug(repipe(p, recalculate=c("a"), parent=envir)), "evaluating a")
  #expect_equal(repipe(p, recalculate=c("a"))$vertices$a$value, a)
  with_mock(f=mock(1,2), {
    #expect_equal(repipe(p, recalculate=c("a"), parent=envir)$vertices$a$value, a)
    expect_equal(pipeExprs(exprs)$vertices$a$value, 1)
    expect_equal(repipe(p, recalculate=c("a"))$vertices$a$value, 2)
  })
})

test_that("repipe reevaluates descendants of specified vertices", {
  with_mock(f=mock(3), {
    r <- repipe(p, recalculate=c("a"), parent.env=envir)
    expect_equal(r$vertices$a$value, 3)
    expect_equal(r$vertices$b$value, 6)
  })
})

test_that("repipe processors match originals", {
  expect_equal(q$processors, p$processors)
})
