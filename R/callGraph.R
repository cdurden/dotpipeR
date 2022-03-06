library(jsonlite)
library(digest)
library(magrittr)
library(Rgraphviz)
library(envnames)
debug_message <- function(...) {
    if (!is.null(getOption("dotpipeR.debug")) && getOption("dotpipeR.debug")) {
        message(...)
    }
}

pipelineDb <- new.env()

catEnvironmentChain <- function(envir) {
    if (address(envir) != address(emptyenv())) {
        catEnvironmentChain(parent.env(envir))
    }
    debug_message(paste0(address(envir),environmentName(envir),"\n"))
}

findNames <- function(x) {
  if (is.atomic(x)) {
      NULL
  } else if (is.name(x)) {
      if (identical(x, substitute())) { # empty symbol
          NULL
      } else {
          deparse(x)
      }
  } else if (is.call(x)) {
      unique(unlist(lapply(x, findNames)))
  } else if (is.pairlist(x)) {
      unique(unlist(lapply(x, findNames)))
  } else {
    stop("Don't know how to handle type ", typeof(x),
      call. = FALSE)
  }
}

findNonArgumentNames <- function(x, exclude=list()) {
  if (is.atomic(x)) {
      NULL
  } else if (is.name(x)) {
      if (identical(x, substitute())) { # empty symbol
          NULL
      } else {
          deparse(x)
      }
  } else if (is.call(x)) {
      unique(unlist(lapply(x, findNonArgumentNames, exclude=exclude)))
  } else if (is.pairlist(x)) {
      unique(unlist(lapply(x, findNonArgumentNames, exclude=names(x))))
  } else {
    stop("Don't know how to handle type ", typeof(x),
      call. = FALSE)
  }
}
findNonArgumentNonAssignmentNames <- function(x, exclude=list()) {
  if (is.atomic(x)) {
      NULL
  } else if (is.name(x)) {
      if (identical(x, substitute())) { # empty symbol
          NULL
      } else {
          deparse(x)
      }
  } else if (is.call(x)) {
      if (identical(x[[1]], quote(`<-`))) {
          unique(unlist(lapply(x[-1:-2], findNonArgumentNonAssignmentNames, exclude=exclude)))
      } else {
          unique(unlist(lapply(x[-1], findNonArgumentNonAssignmentNames, exclude=exclude)))
      }
  } else if (is.pairlist(x)) {
      unique(unlist(lapply(x, findNonArgumentNonAssignmentNames, exclude=names(x))))
  } else {
    stop("Don't know how to handle type ", typeof(x),
      call. = FALSE)
  }
}
findAssignments <- function(x) {
  if (is.atomic(x)) {
      NULL
  } else if (is.name(x)) {
      NULL
  } else if (is.call(x)) {
      if (identical(x[[1]], quote(`<-`))) {
          if (is.name(x[[2]])) {
              c(deparse(x[[2]]),unique(unlist(lapply(x[-1:-2], findAssignments))))
          } else {
              NULL
          }
      } else {
          unique(unlist(lapply(x, findAssignments)))
      }
  } else if (is.pairlist(x)) {
      unique(unlist(lapply(x, findAssignments)))
  } else {
    stop("Don't know how to handle type ", typeof(x),
      call. = FALSE)
  }
}
loadData <- function(file) {
    #debug_message(paste0("Trying to load cached data from '", file, "'\n"))
    if (file.exists(file)) {
        tmpEnv <- new.env()
        load(file=file, envir=tmpEnv)
        if(!exists("x", tmpEnv, inherits=FALSE) || length(tmpEnv)>1) { stop(paste0("R data file ",file," is malformed.")) }
        debug_message("Loaded cached data")
        tmpEnv$x
    } else {
        NULL
    }
}
clearCachedValue <- function(file) {
    if (file.exists(file)) {
        file.remove(file)
    }
}
saveData <- function(x, file) {
    if (!dir.exists(dirname(file))) {
        dir.create(dirname(file), recursive=TRUE)
    }
    save(x, file=file)
}
digestVertex <- function(vertex, inputVertexList) {
    inputVertexList <- getInputs(vertex$name_, vertex$graph)
    inputDigests <- lapply(inputVertexList, function(vertex) vertex$digest)
    vertex$digest <- digest(list(vertex$expression, inputDigests))
    vertex
}
buildCallGraph <- function(x, callGraph, envir=new.env(parent=globalenv()), processors=list(), priorCallGraph=NULL, recalculate=list()) {
    debug_message("building up call graph from expression...")
    debug_message(paste("buildCallGraph received arguments:", paste(lapply(names(formals()), function(arg) { if(!do.call(missing, list(arg), envir=parent.frame(2))) arg }), collapse=", ")))
  if (is.atomic(x)) {
      callGraph
  } else if (is.name(x)) {
      callGraph
  } else if (is.call(x)) {
      names <- findNonArgumentNames(x) # These are names that are not the names of formal arguments to functions
      # FIXME: Should we use findNonArgumentNonAssignmentNames here?
      # Retain, as possible inputs, only those names which exist in the evaluation environment or one of the enclosing frames
      existsInEvalEnvironment <- function(x) {
          exists(x, envir=envir, inherits=FALSE)
      }
      availableNames <- Filter(existsInEvalEnvironment, names)
      # Retain as inputs only those names whose values match values bound to a vertex of the same name in the graph.
      # Why?
      inputNames <- Filter(function(name) identical(callGraph$vertices[[name]]$value, get(name, envir=envir)), availableNames)
      # FIXME: What if one of the input names is the name of a function argument which also matches a symbol in the evaluation environment (or one of its enclosing environments)? If we identify the name of a function argument with a name in an enclosing environment, then we will end up adding to the call graph an incoming edge from a vertex whose data is not used. We can resolve this issue by excluding names of function arguments from our inputs.
      # Note: Another solution may be to simulate the chain of enclosing environments that are created by eval. This approach may be more robust.
      # Perhaps the most robust solution would be to perform eval recursively, simulating the standard environment creation process with each function call, and passing along input/output data along with each return value. This would have the advantage of inherently matching `eval` native behavior of binding variables (assigning values to names?).
      # How would this change the structure of the code? Ideas enumerated below:
      # a. Wrap the eval call with a function that simulates environment creation:
      #   1. On each call, ...
      #   2. Find names and assignments that are used during evaluation, and return this info along with the return value.
      # Try to find a cached value of the expression
      # Find assignment expressions
      assignments <- findAssignments(x)
      # Retain only assignments which are accessible (post evaluation) in the evaluation environment
      outputNames <- Filter(existsInEvalEnvironment, assignments)
      name <- NULL
      if (identical(x[[1]], quote(`<-`))) {
          if (is.name(x[[2]]) && x[[2]] != "self") {
              name <- deparse(x[[2]])
              newEdges <- lapply(inputNames, function(inputVertexName) list(inputVertexName, name))
              callGraph$edges <- addEdges(callGraph$edges, newEdges)
              vertex <- list(expression=x, graph=callGraph, envir=envir, foreign=FALSE)

              for (f in processors$eval$pre) {
                  vertex <- f(vertex)
              }
              debug_message(paste0(name, "\n"))
              if (name %in% union(recalculate,descendantsOf(callGraph, recalculate)) || is.null(vertex$cache)) {
                  debug_message(paste0("evaluating ",name))
                  debug_message(vertex$cache)
                  value <- eval(x, envir=envir)
              } else {
                  value <- vertex$cache
              }
              vertex$value <- value
              if (name %in% recalculate) {
                  debug_message(paste0("recalculation forced for ", name))
              }
              # FIXME: using inherits = TRUE prevents names from being set if they are already set in an enclosing environment.
              # This also causes conflicts between separate pipes which are run in sequence.
              # FIXME: Why?
              if (!exists(name, envir, inherits = FALSE)) {
                  assign(name, value, envir=envir)
              }
              vertex$name_ <- name
              for (f in processors$eval$post) {
                  vertex <- f(vertex)
              }
              callGraph$vertices[[name]] <- vertex
              callGraph
          } else { # How does this happen? This happens, for example, if the LHS of the assignment operator is a call.
              debug_message(paste0("Evaluating ",as.character(x),"in environment\n"))
              eval(x, envir=envir)
              callGraph #This should return the same environment as envir$self
          }
      } else {
          eval(x, envir=envir)
          callGraph
      }
  } else if (is.pairlist(x)) {
      #debug_message(paste0("Expression is pairlist\n"))
      callGraph <- Reduce(function(g, y) buildCallGraph(y, g, envir=envir, processors=processors, priorCallGraph=priorCallGraph, recalculate=recalculate), x, callGraph)
      #debug_message(paste0("Vertices: ",paste(lapply(as.list(callGraph$vertices), `[[`, "name")),"\n"))
      callGraph
  } else {
    stop("Don't know how to handle type ", typeof(x),
      call. = FALSE)
  }
}
setSelf <- function(g, name="self") {
    assign(name, g, parent.frame())
    g$selfName <- name
    g
}
inheritParentProcessors <- function(g, name="self") {
    parentPipeline <- parent.env(parent.frame())[[name]]
    if (is.callGraph(parentPipeline)) {
        processors <- mergeLists(parentPipeline$args$processors, processors)
    }
    g
}
setId <- function(g, id=sub("/","",tempfile("","")), overwrite=FALSE) {
    if (!is.null(g$id) && !overwrite) return(g)
    if (is.function(id)) {
        g$id <- id(g)
    } else if (is.character(id) || is.numeric(id)) {
        g$id <- id
    }
    g
}
setDir <- function(g, prefix=tempdir(), dir=NULL) {
    if (is.null(dir)) {
        dir <- g$id
    }
    g$dir <- file.path(prefix, dir)
    g
}

getUrl <- function(file, base_dir=tempdir(), base_url="./Rtmp") {
    path <- basename(file)
    dir <- dirname(file)
    while (dir != base_dir) {
        if (dir == "/" || dir == "." || dir == "") {
            stop("File not found in base_dir")
        }
        path <- file.path(basename(dir),path)
        dir <- dirname(dir)
    }
    url <- file.path(base_url, path)
    url
}
exportGraph <- function(g, prefix=g$dir) {
    if(!dir.exists(prefix)) {
        dir.create(prefix)
    }
    g$vertices <- lapply(g$vertices, function(vertex) exportVertexData(vertex, prefix=prefix))
    #debug_message(paste0("Writing dot to ", file.path(prefix, g$id), "\n"))
    #debug_message(paste0("Vertices: ",names(g$vertices),"\n"))
    #debug_message(paste0("Edges: \n"))
    write.dot(g, file.path(prefix, g$id))
    g
}
# FIXME: This function requires the vertex to have a digest already.
# It does not make sense to use a digest that depends on the value at a vertex
loadVertexFromCache <- function(vertex) {
    cacheFile <- vertexCacheFile(vertex)
    debug_message(paste0("Trying to load vertex cache from file",cacheFile))
    if (file.exists(cacheFile)) {
        debug_message(paste0("Cache file exists"))
    }
    vertex$cache = loadData(cacheFile)
    vertex
}
vertexCacheFile <-function(vertex) {
    file.path(vertex$graph$dir,"cache",vertex$digest)
}
saveVertexToCache <- function(vertex) {
    #debug_message(paste0("Saving vertex data to cache\n"))
    saveData(vertex$value, vertexCacheFile(vertex))
    vertex
}
exportVertexData <- function(vertex, prefix=tempdir()) {
    exportData <- function(x, reprFile) {
        metadata <- list()
        #debug_message(paste0("Writing vertex data to ", reprFile, "\n"))
        if (is.checkpoint(x)) {
            # FIXME: The file name can be a digest of the data value
            write(as.character(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile)), style="filled", fillcolor=if (all(x)) "green" else "red"))
        } else if (is.numeric(x)) {
            # FIXME: The file name can be a digest of the data value
            write(as.character(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is.character(x)) {
            write(x, reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is.function(x)) {
            write(deparse(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is(x, "dropbox")) {
            writeLines(x$schemaJson, reprFile)
            href <- paste0("?file=",getUrl(reprFile),"&module=./dropbox.js&dropboxId=",x$id,"&redirectUrl=",URLencode(x$redirectUrl,reserved=TRUE))
            metadata <- append(metadata,list(href=href))
        } else if (is.data.frame(x)) {
            write.csv(x, reprFile)
        } else if (is(x, "callGraph")) {
            write.dot(x, path=reprFile)
            href <- paste0("?file=",getUrl(reprFile),"&handler=dotViewer")
            metadata <- append(metadata,list(href=href))
        } else if (is.list(x)) {
            #debug_message(paste0("List length ",length(x),"\n"))
            urls <- lapply(x, function(item) {
                #debug_message(paste0("List item has class ",class(item),"\n"))
                reprFile <- file.path(prefix, digest(list(x,item)))
                metadata <- exportData(item, reprFile)
                return(metadata$href)
            })
            writeLines(toJSON(urls, auto_unbox=TRUE), reprFile)
            href <- paste0("?file=",getUrl(reprFile),"&module=./url-list.js")
            metadata <- append(metadata,list(href=href))
        }
        #debug_message(paste0("Metadata href: ",metadata$href,"\n"))
        return(metadata)
    }
    metadata <- vertex$value %>% (function(x) exportData(x, file.path(prefix,digest(x))))
    vertex <- append(vertex, metadata)
    #debug_message(paste0("Vertex: ", vertex$name, "\n"))
    #debug_message(paste0("Vertex metadata attributes: \n"))
    #debug_message(paste0(names(vertex),"\n"))

    # For saving graphics as objects: https://stackoverflow.com/a/29583945/13130147
    # The method described above seems to require calling plot and then calling
    # additional functions that record the graphics object.
    # Perhaps plot saving functionality can be integrated via transformation
    # performed on `plot` calls when the source code is parsed.
    vertex
}
# This function triggers an event that is used to initiate
# reprocessing of pipelines which include other pipelines.
# The event object will include the target pipeline,
# which is the pipeline whose parent we would like to update.
# We need to use this in combination with handlers that
# listen for pipelineProcessed events on this target,
clearPipelineEventHandlers <- function(g) {
    debug_message(paste0("Clearing event handlers for pipeline",g$id,"\n"))
    clearEventHandlers(g$id)
    g
}
clearPipelineVertexEventHandlers <- function(vertex, x = vertex$value) {
    if (is(x, "callGraph")) {
        clearPipelineEventHandlers(x)
    } else if (is.list(x)) {
        lapply(x, function(item) clearPipelineVertexEventHandlers(vertex, item))
    }
    vertex
}
storePipeline <- function(g) {
    if(!is.null(g$id)) {
        pipelineDb[[g$id]] <- g
    }
    g
}
triggerPipelineProcessedEvent <- function(g) {
    triggerEvent(list(target=g$id, type="pipelineProcessed"))
    g
}
is.callGraph <- function(x) {
    is(x, "callGraph")
}
addUpdatePipelineVertexHandler <- function(vertex) {
    x <- vertex$value
    if (is(x, "callGraph")) {
        addEventHandler(x$id, "pipelineProcessed", function(event) {
            debug_message(paste0("Updating parent pipeline\n"))
            newValue <- pipelineDb[[x$id]]
            vertex$graph$vertices[[vertex$name_]]$value <- newValue
            vertex$graph$vertices[[vertex$name_]]$digest <- 0
            #repipe(vertex$graph)
        })
        #debug_message(paste0("Pipeline vertex added repipe parent 'pipelineProcessed' event handler\n"))
    } else if (is.list(x)) {
        lapply(x, function(item) {
            if (is.callGraph(item)) {
                addEventHandler(item$id, "pipelineProcessed", function(event) {
                    debug_message(paste0("Updating parent pipeline\n"))
                    newValue <- pipelineDb[[item$id]]
                    i <- which(sapply(vertex$graph$vertices[[vertex$name_]]$value, function(y) is.callGraph(y) && y$id == item$id))
                    vertex$graph$vertices[[vertex$name_]]$value[[i]] <- newValue
                    inputVertexList <- getInputs(vertex$name_, vertex$graph)
                    vertex$graph$vertices[[vertex$name_]]$digest <- digestVertex(vertex$graph$vertices[[vertex$name_]], inputVertexList) # FIXME: Can we remove this explicit call to a particular digest function?
                    repipe(vertex$graph)
                })
            }
        })
    }
    vertex
}
addRepipeParentHandlerOnPipelineVertex <- function(vertex, x = vertex$value) {
    #debug_message(paste0("vertex",vertex$name_,"data is a",class(x),"\n"))
    if (is(x, "callGraph")) {
        addEventHandler(x$id, "pipelineProcessed", function(event) {
            debug_message(paste0("Repiping pipeline",vertex$graph$id," which contains pipeline",x$id,"at vertex ",vertex$name_,"\n"))
            repipe(vertex$graph, recalculate=vertex$name_)
        })
        #debug_message(paste0("Pipeline vertex added repipe parent 'pipelineProcessed' event handler\n"))
    } else if (is.list(x)) {
        lapply(x, function(item) addRepipeParentHandlerOnPipelineVertex(vertex, item))
    }
    vertex
}
repipeParentIfModified <- function(vertex) {
    debug_message(paste0("vertex",vertex$name_,"changed?",vertex$changed,"\n"))
    if (vertex$changed) {
        repipe(vertex$graph, recalculate=vertex$name_)
    }
    vertex
}
defaultPipe <- function() {
                 list(
                           pre=list(setId, setDir, setSelf, setParent, inheritParentProcessors),
                           post=list()
                 )
}
defaultEval <- function() {
                 list(
                           pre=list(digestVertex, loadVertexFromCache),
                           post=list(saveVertexToCache)
                 )
}
defaultProcessors <- function(reactive=exists("triggerEvent")) {
    processors <- list(pipe=defaultPipe(),eval=defaultEval())
    if (reactive) {
        processors$pipe$post <- union(processors$pipe$post, list(storePipeline, triggerPipelineProcessedEvent))
        processors$eval$post <- union(processors$eval$post, list(clearPipelineVertexEventHandlers, addUpdatePipelineVertexHandler))
    }
    processors
}
buildProcessors <- function(prePipe=list(), postPipe=list(), preEval=list(), postEval=list(), extras=list(), ..., initial=defaultProcessors(...)) {
    mergeLists(
        mergeLists(
            list(pipe=list(pre=prePipe,post=postPipe), eval=list(pre=preEval,post=postEval)),
            extras
        ),
        initial,
    )
}
setParent <- function(g, name="self") {
    g$parent <- g$args$parent.env[[name]]
}
getParent <- function(g) {
    g$parent
}
pipeExprs <- function(exprs, parent.env=globalenv(), params=list(), processors=buildProcessors(), priorCallGraph=NULL, recalculate=list()) {
    debug_message("piping...")
    g <- list2env(list(vertices=list(), edges=list()))
    class(g) <- "callGraph"
    if(!is.null(priorCallGraph)) {
        g$id <- priorCallGraph$id
    }
    envir <- new.env(parent=parent.env)
    lapply(names(params), function(paramName) assign(paramName, params[[paramName]], envir=envir))
    g$args <- list()
    argNames <- Filter(function(name) !(name %in% c("...")),
                       names(formals(pipeExprs)))
    lapply(argNames, function(name) {
        g$args[[name]] <- get(name)
    })

    for (f in processors$pipe$pre) {
        do.call(f, list(g), envir=envir)
    }
    callGraph <- Reduce(function(g, y) {
        debug_message("calling buildCallGraph...")
        buildCallGraph(y, g, envir, processors=processors, priorCallGraph=priorCallGraph, recalculate=recalculate)
    }, exprs, init=g)
    for (f in processors$pipe$post) {
        callGraph <- f(callGraph)
    }
    callGraph
}
pipe <- function(file, ...) {
    debug_message(paste0("-----------------------------------------------\n"))
    debug_message(paste0("Piping ", file, "\n"))
    exprs <- parse(file);
    g <- pipeExprs(exprs, ...)
    debug_message(paste0("-----------------------------------------------\n\n"))
    g
}
take <- function(names_, ...) {
    lists <- list(...)
    results <- lapply(names_, function(name) {
        i <- min(which(sapply(lists, function(list_) name %in% names(list_))))
        lists[[i]][[name]]
    })
    names(results) <- names_
    results
}
mergeLists <- function(a, b, joiner=c) {
    Reduce(function(result, name) {
        if (is.list(a[[name]]) && is.list(b[[name]])) {
            result[[name]] <- mergeLists(a[[name]],b[[name]], joiner)
        } else if (name == "") {
            result <- append(result, joiner(a[names(a)==""],b[names(b)==""]))
        } else {
            result[[name]] <- joiner(a[[name]],b[[name]])
        }
        result
    }, union(names(a),names(b)), joiner(if(is.null(names(a))) a, if(is.null(names(b))) b))
}

repipe <- function(priorCallGraph, ...) {
    debug_message("repiping...")
    #debug_message(paste0("callGraph id before repipe:", priorCallGraph$id,"\n"))

    argNames <- union(names(priorCallGraph$args),names(list(...)))
    args <- take(argNames, list(...), priorCallGraph$args)
    args$priorCallGraph <- priorCallGraph

    g <- do.call(pipeExprs, args)
}
as.graph <- function(callGraph) {
    library(graph)
    g <- new("graphNEL", nodes=names(callGraph$vertices), edgemode="directed")
    for (edge in callGraph$edges) {
        g <- addEdge(edge[[1]], edge[[2]], g, 1)
    }
    g
}

write.dot <- function(g, path=file.path(dir,paste0(g$id,".dot")), dir=tempdir()) {
    defaultAttrs <- list(node=list(href="#",cacheKey="",style="filled",fillcolor="transparent"))
    nAttrs <- Reduce(function(nAttrs, attr) { nAttrs[[attr]] <- lapply(Filter(function(v) !is.null(v[[attr]]), g$vertices), function(v) v[[attr]]); nAttrs }, names(defaultAttrs$node), list())
    toDot(as.graph(g), path, nodeAttrs=nAttrs, attrs=defaultAttrs)
    path
}

# Visualize with: https://github.com/magjac/d3-graphviz
clearCache <- function(g, ...) {
    for (vertex in g$vertices) {
        clearCachedValue(file.path(g$dir,"cache",vertex$cacheKey), ...)
    }
}
restrict <- function(g, vertices) {
    h <- rlang::env_clone(g)
    h$vertices <- g$vertices[names(g$vertices) %in% names(vertices)]
    h$edges <- Filter(function(edge) edge[[1]] %in% names(h$vertices) && edge[[2]] %in% names(h$vertices), h$edges)
    h
}
getInputs <- function(vertexName, callGraph) {
    inputEdges <- Filter(function(edge) edge[[2]] == vertexName, callGraph$edges)
    inputNames <- lapply(inputEdges, function(edge) edge[[1]])
    inputs <- lapply(inputNames, function(name) callGraph$vertices[[name]])
    names(inputs) <- inputNames
    inputs
}
addEdges <- function(oldEdges, newEdges) {
    edges <- append(oldEdges, newEdges)
    names(edges) <- unlist(lapply(edges, function(edge) paste(edge[[1]],edge[[2]],sep="~")))
    edges
}
childrenOf <- function(g, vertexNames) {
    lapply(Filter(function(edge) edge[[1]] %in% vertexNames, g$edges), `[[`, 2)
}
descendantsOf <- function(g, vertexNames) {
    children <- childrenOf(g, vertexNames)
    Reduce(function(descendants, childName) union(descendants, descendantsOf(g, childName)), children, init=children)
}
maximalVertices <- function(g) {
    singletonNames <- Filter(function(vertexName) !(vertexName %in% unlist(g$edges)), names(g$vertices))
    predecessorNames <- sapply(g$edges, function(edge) edge[[1]])
    maximalNames <- unique(append(singletonNames, unlist(Filter(function(vertexName) !(vertexName %in% lapply(g$edges, function(edge) edge[[2]])), predecessorNames))))
    mget(maximalNames, list2env(g$vertices))
}
minimalVertices <- function(g) {
    singletonNames <- Filter(function(vertexName) !(vertexName %in% unlist(g$edges)), names(g$vertices))
    predecessorNames <- sapply(g$edges, function(edge) edge[[1]])
    minimalNames <- unique(append(singletonNames, unlist(Filter(function(vertexName) !(vertexName %in% lapply(g$edges, function(edge) edge[[1]])), predecessorNames))))
    mget(minimalNames, list2env(g$vertices))
}
cartesianProduct <- function(x,y) {
    #debug_message(paste0("x:",x,"\n"))
    #debug_message(paste0("y:",y,"\n"))
    as.data.frame(t(merge(x,y)))
}

embed <- function(g, h, below, above, prefix=paste0(h$id,"::")) {
    #debug_message(paste0("Embedding\n"))
    if (missing(below)) {
        if (is.language(h)) {
            below <- Filter(function(vertex) vertex %in% findNames(h), names(g$vertices))
        }
    }
    if (missing(above)) {
        if (is.language(h)) {
            #browser()
            above <- names(g$vertices[unlist(lapply(Filter(function(edge) edge[[1]] %in% below, g$edges), function(edge) edge[[2]]))])
            #debug_message(paste0("Above: ",names(above),"\n"))
        }
    }
    #debug_message(paste0("Embedding h in g\n"))
    if (is.language(h)) {
        h <- eval(h, envir=g$envir)
    }
    if (is.list(h)) {
        g <- Reduce(function(g, x) embed(g, x, below=below, above=above), h, g)
    } else {
        vertices <- lapply(h$vertices, function(vertex) {
            vertex$foreign <- TRUE
            vertex
        })
        newVertices <- rename(vertices, paste0(prefix, names(vertices)))
        g$vertices <- append(g$vertices, newVertices)
        g$edges <- addEdges(g$edges, append(cartesianProduct(below, paste0(prefix,names(maximalVertices(h)))), cartesianProduct(paste0(prefix,names(minimalVertices(h))), above)))
        g
    }
}
rename <- function(x, newNames) {
    #debug_message(paste0("names(x):",names(x),"\n"))
    #debug_message(paste0("new names:",make.names(newNames),"\n"))
    names(x) <- newNames
    x
}
after <- function(x, y) y
`%then%` <- function(x, y) {
    y
}
checkpoint <- function(x) {
    if(!is.logical(x)) stop("argument x passed to checkpoint is not logical")
    class(x) <- "checkpoint"
    x
}
is.checkpoint <- function(x) {
    class(x) == "checkpoint"
}
