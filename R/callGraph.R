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
        #browser()
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
    #debug_message(paste0(paste0("Caching value at ",file,"\n")))
    if (!dir.exists(dirname(file))) {
        dir.create(dirname(file), recursive=TRUE)
    }
    save(x, file=file)
}
digestVertex <- function(vertex, inputVertexList) {
    #inputDigests <- lapply(inputVertexList, function(vertex) digest(vertex$value))
    #inputVertexList <- lapply(inputNames, function(inputVertexName) callGraph$vertices[[inputVertexName]])
    inputVertexList <- getInputs(vertex$name_, vertex$graph)
    #vertex$digest <- digestVertex(vertex, inputVertexList)
    inputDigests <- lapply(inputVertexList, function(vertex) vertex$digest)
    vertex$digest <- digest(list(vertex$expression, inputDigests))
    #vertex$digest <- digest(list(vertex$value, inputDigests))
    vertex
}
buildCallGraph <- function(x, callGraph, envir=new.env(parent=globalenv()), processors=list(), priorCallGraph=NULL, recalculate=list()) {
    debug_message("building up call graph from expression...")
    debug_message(paste("buildCallGraph received arguments:", paste(lapply(names(formals()), function(arg) { if(!do.call(missing, list(arg), envir=parent.frame(2))) arg }), collapse=", ")))
    #debug_message(paste0(tracemem(callGraph), "\n"))
    #debug_message(paste0("buildCallGraph environment: ", address(envir), "\n"))
  #debug_message(paste0("\n"))
  #debug_message(paste0("\n"))
  #debug_message(paste0("Adding expression to call graph:",as.character(x),"\n"))
  #debug_message(paste0("Input call graph vertices: ",paste(names(callGraph$vertices)),"\n"))
  if (is.atomic(x)) {
      #debug_message(paste0("Expression is atomic\n"))
      callGraph
  } else if (is.name(x)) {
      #debug_message(paste0("Expression is name\n"))
      callGraph
  } else if (is.call(x)) {
      #debug_message(paste0("Expression is call\n"))
      names <- findNonArgumentNames(x) # These are names that are not the names of formal arguments to functions
      # FIXME: Should we use findNonArgumentNonAssignmentNames here?
      # Retain, as possible inputs, only those names which exist in the evaluation environment or one of the enclosing frames
      existsInEvalEnvironment <- function(x) {
          exists(x, envir=envir, inherits=FALSE)
      }
      availableNames <- Filter(existsInEvalEnvironment, names)
      # Retain as inputs only those names whose values match values bound to a vertex of the same name in the graph.
      # Why?
#      getVertexByName <- function(name) {
#          callGraph$vertices[[name]]
##          with(
##              list(results=Filter(function(v) {
##                  return(v$name==name)
##              }, as.list(callGraph$vertices))),
##              if (length(results)>0) {
##                  results[[1]]
##              } else {
##                  NULL
##              }
##          )
#      }
#      vertexBindsObject <- function(vertex, name, obj) {
#          #debug_message(paste0("Checking object against object bound to vertex", v$name, "\n"))
#          identical(obj, get(name, envir=vertex$envir))
#      }
#      inputNames0 <- Filter(function(name) with(list(vertex=getVertexByName(name)), if (!is.null(vertex)) vertexBindsObject(vertex, name, get(name, envir=envir)) else FALSE), availableNames)
      inputNames <- Filter(function(name) identical(callGraph$vertices[[name]]$value, get(name, envir=envir)), availableNames)
#      debug_message(paste0("Input names",inputNames,"\n"))
#      debug_message(paste0("Input names 0",inputNames0,"\n"))
      # FIXME: What if one of the input names is the name of a function argument which also matches a symbol in the evaluation environment (or one of its enclosing environments)? If we identify the name of a function argument with a name in an enclosing environment, then we will end up adding to the call graph an incoming edge from a vertex whose data is not used. We can resolve this issue by excluding names of function arguments from our inputs.
      # Note: Another solution may be to simulate the chain of enclosing environments that are created by eval. This approach may be more robust.
      # Perhaps the most robust solution would be to perform eval recursively, simulating the standard environment creation process with each function call, and passing along input/output data along with each return value. This would have the advantage of inherently matching `eval` native behavior of binding variables (assigning values to names?).
      # How would this change the structure of the code? Ideas enumerated below:
      # a. Wrap the eval call with a function that simulates environment creation:
      #   1. On each call, ...
      #   2. Find names and assignments that are used during evaluation, and return this info along with the return value.
      #debug_message(paste0("Inputs:", paste(inputNames), "\n"))
      # Try to find a cached value of the expression
      #inputVertexList <- lapply(inputNames, function(inputVertexName) getVertexByName(inputVertexName))
      #cacheKey <- digest(list(x, inputDigests)) # FIXME: The digests of some inputs (e.g. functions) will depend on the environment to which they are bound, which will change between runs.
      # Find assignment expressions
      assignments <- findAssignments(x)
      # Retain only assignments which are accessible (post evaluation) in the evaluation environment
      outputNames <- Filter(existsInEvalEnvironment, assignments)
      #outputVertexList <- as.set(lapply(outputNames, function(name) with(list(vertex=getVertexByName(name)), if(!is.null(vertex)) vertex else list(name=name, envir=envir, callData=NULL))))
      name <- NULL
      if (identical(x[[1]], quote(`<-`))) {
          if (is.name(x[[2]]) && x[[2]] != "self") {
              name <- deparse(x[[2]])
              newEdges <- lapply(inputNames, function(inputVertexName) list(inputVertexName, name))
              callGraph$edges <- addEdges(callGraph$edges, newEdges)
              vertex <- list(expression=x, graph=callGraph, envir=envir, foreign=FALSE)
              #vertex <- list(graph=callGraph, digest=digest(list(x[[3]], inputDigests)), envir=envir, foreign=FALSE) #FIXME: COuld we us this instead?

              for (f in processors$eval$pre) {
                  vertex <- f(vertex)
              }
              debug_message(paste0(name, "\n"))
              if (name %in% union(recalculate,descendantsOf(callGraph, recalculate)) || is.null(vertex$cache)) {
                  #debug_message(paste0("Evaluating vertex", name, "\n"))
                  debug_message(paste0("evaluating ",name))
                  debug_message(vertex$cache)
                  #browser()
                  value <- eval(x, envir=envir)
                  #value <- eval(x, envir=envir) #FIXME: COuld we us this instead?
                  #vertex$changed <- TRUE
              } else {
                  value <- vertex$cache
                  #vertex$changed <- FALSE
              }
              #callData <- list2env(list(value=value, expression=x))
              #debug_message(paste0("Expression's value has class", class(value), "\n"))
              vertex$value <- value
              if (name %in% recalculate) {
                  debug_message(paste0("recalculation forced for ", name))
              }
#              debug_message(paste0("priorCallGraph has vertices:",names(priorCallGraph$vertices),"\n"))
#              debug_message(paste0("prior value:", show(priorCallGraph$vertices[[name]]$callData$value), "\n"))
#              debug_message(paste0("current value:", show(value), "\n"))
#              vertex$modified <- name %in% names(priorCallGraph$vertices) && digest(priorCallGraph$vertices[[name]]$callData$value) != digest(value)
#              browser();
#              if (vertex$modified) {
#                  #browser();
#              }
              #debug_message(paste0("Assignment to", name,"\n"))
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
              #vertexList <- list(vertex)
              #names(vertexList) <- c(vertex$name)
              #callGraph$vertices <- append(callGraph$vertices,vertexList)
              #debug_message(paste0("Vertex name",vertex$name,"\n"))
              callGraph$vertices[[name]] <- vertex
              #debug_message(paste0("Adding edges to graph",inputNames,"\n"))
              #callGraph$edges <- append(callGraph$edges,newEdges)
              callGraph
#          } else if (is.call(x[[2]])) {
#              value <- eval(x[[3]], envir=envir)
#              subexpr <- x[[2]]
#              if (identical(subexpr[[1]], quote(`$`))) {
#                  if (subexpr[[2]] == "self") {
#                      debug_message(paste0(paste0("Assigning value to self[[",subexpr[[3]],"]]\n")))
#                      debug_message(paste0("Value has class", class(value)))
#                      debug_message(paste0("Length: ", length(value)))
#                      debug_message(paste0("Names: ", names(value)))
#                      #`[[<-`(callGraph, subexpr[[3]], value)
#                      callGraph[[subexpr[[3]]]] <- value
#                      debug_message(paste0("Names: ", names(callGraph[[subexpr[[3]]]])))
#                  }
#              }
#              callGraph
          } else { # How does this happen? This happens, for example, if the LHS of the assignment operator is a call.
              debug_message(paste0("Evaluating ",as.character(x),"in environment\n"))
              eval(x, envir=envir)
              #envir$self
              callGraph #This should return the same environment as envir$self
          }
      } else {
          #debug_message(paste0("Expression is not assignment\n"))
          eval(x, envir=envir)
          #debug_message(paste0("Vertices: ",paste(lapply(as.list(callGraph$vertices), `[[`, "name")),"\n"))
          #debug_message(paste0("Vertices: ",names(callGraph$vertices),"\n"))
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
    #show(g$edges)
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
    } else {
        #browser()
    }
    vertex$cache = loadData(cacheFile)
    vertex
}
vertexCacheFile <-function(vertex) {
    file.path(vertex$graph$dir,"cache",vertex$digest)
}
saveVertexToCache <- function(vertex) {
    #debug_message(paste0("Saving vertex data to cache\n"))
    #browser()
    saveData(vertex$value, vertexCacheFile(vertex))
    vertex
}
exportVertexData <- function(vertex, prefix=tempdir()) {
    #reprFile <- NULL
    exportData <- function(x, reprFile) {
        #metadata <- list(reprFile=reprFile)
        metadata <- list()
        #debug_message(paste0("Writing vertex data to ", reprFile, "\n"))
        if (is.checkpoint(x)) {
            # FIXME: The file name can be a digest of the data value
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".txt"))
            write(as.character(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile)), style="filled", fillcolor=if (all(x)) "green" else "red"))
        } else if (is.numeric(x)) {
            # FIXME: The file name can be a digest of the data value
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".txt"))
            write(as.character(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is.character(x)) {
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".txt"))
            write(x, reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is.function(x)) {
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".txt"))
            write(deparse(x), reprFile)
            metadata <- append(metadata,list(mimetype="text", href=paste0("?file=",getUrl(reprFile))))
        } else if (is(x, "dropbox")) {
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".json"))
            #vertex$href <- paste0("?file=",reprFile,"&module=./dropbox.js&dropboxId=",x$id,"&redirectUrl=",x$redirectUrl)
            writeLines(x$schemaJson, reprFile)
            href <- paste0("?file=",getUrl(reprFile),"&module=./dropbox.js&dropboxId=",x$id,"&redirectUrl=",URLencode(x$redirectUrl,reserved=TRUE))
            metadata <- append(metadata,list(href=href))
        } else if (is.data.frame(x)) {
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".csv"))
            write.csv(x, reprFile)
        } else if (is(x, "callGraph")) {
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".dot"))
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
            #reprFile <- file.path(reprFilePrefix, paste0(vertex$digest,".json"))
            writeLines(toJSON(urls, auto_unbox=TRUE), reprFile)
            href <- paste0("?file=",getUrl(reprFile),"&module=./url-list.js")
            metadata <- append(metadata,list(href=href))
            #vertex$href <- paste0("?file=",reprFile,"&module=./file-list.js&dropboxId=",x$id,"&redirectUrl=",x$redirectUrl)
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
#    if (missing(x)) {
#        x <- vertex$callData$value
#    }
#    debug_message(paste0("vertex",vertex$name_,"data is a",class(x),"\n"))
#    if (is(x, "callGraph")) {
#        addEventHandler(x$id, "pipelineProcessed", function(event) {
#            debug_message(paste0("Repiping pipeline at vertex ",vertex$name_,"\n"))
#            repipe(vertex$envir$self, recalculate=vertex$name_)
#        })
#        debug_message(paste0("Pipeline vertex added repipe parent 'pipelineProcessed' event handler\n"))
#    } else if (is.list(x)) {
#        lapply(x, function(item) addRepipeParentOnPipelineProcessedEventHandler(vertex, item))
#    }
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
            #       list(),
            extras
        ),
        initial,
    )
}
setParent <- function(g, name="self") {
    #g$args$parent$self
    g$parent <- g$args$parent.env[[name]]
}
getParent <- function(g) {
    #g$args$parent$self
    g$parent
}
pipeExprs <- function(exprs, parent.env=globalenv(), params=list(), processors=buildProcessors(), priorCallGraph=NULL, recalculate=list()) {
    debug_message("piping...")
    g <- list2env(list(vertices=list(), edges=list()))
    class(g) <- "callGraph"
    if(!is.null(priorCallGraph)) {
        g$id <- priorCallGraph$id
        #browser()
    }
    envir <- new.env(parent=parent.env)
    lapply(names(params), function(paramName) assign(paramName, params[[paramName]], envir=envir))
    #g$args <- new.env()
    g$args <- list()
    #g$envir <- new.env(parent=envir)
    #argNames <- discard(names(formals(pipeExprs)), function(name) name %in% c("envir", "..."))
    #argNames <- Filter(function(name) !(name %in% c("parent", "...")),
    #                   names(formals(pipeExprs)))
    argNames <- Filter(function(name) !(name %in% c("...")),
                       names(formals(pipeExprs)))
    lapply(argNames, function(name) {
        g$args[[name]] <- get(name)
        #assign(name, get(name), g$args)
    })
    #extraArgNames <- names(list(...))
    #debug_message(paste0("...=list(",paste(extraArgNames,collapse=", "),")"))
    #lapply(extraArgNames, function(name) {
    #    g$args[[name]] <- list(...)[[name]]
    #})
#    g$params <- params
#    g$envir <- envir
#    g$exprs <- exprs
#    g$reactive <- reactive
#    g$inheritProcessors <- inheritProcessors

    # Set up RNG
#    if (!is.null(seed)) {
#        .GlobalEnv$.Random.seed <- seed
#    }
#    if (!exists(".Random.seed", .GlobalEnv)) {
#        runif(1)
#    }
#    if (exists(".Random.seed", .GlobalEnv)) {
#        g$seed <- .GlobalEnv$.Random.seed
#    } else {
#        stop("A RNG seed could not be found")
#    }
    # FIXME: All these preProcessor and postProcessor arguments make for cluttered code
    # merge them all into one processors argument
    #debug_message(paste0(show(envir$self$processors$pipe$pre)))
    #debug_message(paste0(show(processors$pipe$pre)))
    #g$processors <- processors
    #debug_message(paste0("Environment passed to pipeExprs: ",address(envir),"\n"))
    #show(exprs)
    #show(g$exprs)
    #debug_message("running pipe preprocessors...")
    for (f in processors$pipe$pre) {
        #g <- f(g)
        do.call(f, list(g), envir=envir)
    }
    #recalculate <- union(recalculate, descendantsOf(g,recalculate))
    #debug_message("building call graph...")
    #envir$self <- g # We accomplish this using a preprocessor instead
    callGraph <- Reduce(function(g, y) {
        #g <- buildCallGraph(y, g, envir=envir, processors=processors, priorCallGraph=priorCallGraph, ...)
        #partialBuildCallGraph <- partial(buildCallGraph, y, g, envir)
        debug_message("calling buildCallGraph...")
        #g <- buildCallGraph(y, g, envir, processors=processors, priorCallGraph=priorCallGraph, ...)
        buildCallGraph(y, g, envir, processors=processors, priorCallGraph=priorCallGraph, recalculate=recalculate)
    }, exprs, init=g)
#    callGraph$processors$pipe$pre <- processors$pipe$pre
#    callGraph$processors$pipe$post <- processors$pipe$post
#    callGraph$processors$vertex$pre <- processors$vertex$pre
#    callGraph$processors$vertex$post <- processors$vertex$post
    #debug_message("running post-processors...")
    for (f in processors$pipe$post) {
#        environment(f) <- envir
        #debug_message(paste0(deparse(f)))
        callGraph <- f(callGraph)
    }
    #context <- parent.env(environment())
    #context[[callGraph$id]] <- callGraph
    #envir$self <- callGraph
#    environment(onComplete) <- envir
    #debug_message(paste0("pipe complete\n"))
#    onComplete()
    #debug_message(paste0("callback finished\n"))
    callGraph
}
#environment(pipeExprs) <- new.env()
pipe <- function(file, ...) {
    debug_message(paste0("-----------------------------------------------\n"))
    debug_message(paste0("Piping ", file, "\n"))
    exprs <- parse(file);
    #debug_message(paste0(tracemem(g), "\n"))
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
#mergeLists <- function(a, b, joiner=c, mergeNonLists=FALSE) {
mergeLists <- function(a, b, joiner=c) {
    # mergeNonLists=FALSE: If a named element from a is not a list, use the value of that element of as the value mapped to that name in the result
    #browser()
    Reduce(function(result, name) {
        if (is.list(a[[name]]) && is.list(b[[name]])) {
            result[[name]] <- mergeLists(a[[name]],b[[name]], joiner)
        } else if (name == "") {
            result <- append(result, joiner(a[names(a)==""],b[names(b)==""]))
        } else {
#        } else if (mergeNonLists) {
            result[[name]] <- joiner(a[[name]],b[[name]])
#            result[[name]] <- a[[name]]
        }
        result
    }, union(names(a),names(b)), joiner(if(is.null(names(a))) a, if(is.null(names(b))) b))
}

repipe <- function(priorCallGraph, ...) {
    debug_message("repiping...")
    #debug_message(paste0("callGraph id before repipe:", priorCallGraph$id,"\n"))
    #g <- new.env()
    #g$envir <- priorCallGraph$envir # This is necessary so that we can access a parent graph via envir$self.
#    g$id <- priorCallGraph$id
#    g$params <- priorCallGraph$params
#    g$processors <- priorCallGraph$processors

#    args <- list()
#    membersToCopy <- keep(names(priorCallGraph), function(name) (name %in% c("exprs", "params", "processors")))
#    lapply(membersToCopy, function(name) {
#        args[[name]] <<- priorCallGraph[[name]]
#    })

    #g$vertices <- list()
    #g$edges <- list()
    #exprs <- lapply(discard(priorCallGraph$vertices, `[[`, "foreign"), function(vertex) vertex$callData$expression)
    #pipeExprs(g, exprs, processors$pipe$pre=processors$pipe$pre, ...)
    #f <- partial(pipeExprs, ... = , envir=envir, priorCallGraph=priorCallGraph)
    #do.call(f, mget(names(formals(pipeExprs)), g, ifnotfound=formals(pipeExprs)))
    argNames <- union(names(priorCallGraph$args),names(list(...)))
    args <- take(argNames, list(...), priorCallGraph$args)
    args$priorCallGraph <- priorCallGraph
    #browser()
    #show(names(args))
    #args <- mergeLists(priorCallGraph$args, list(...))
    #args$priorCallGraph <- NULL
    #args <- lapply(intersect(discard(names(priorCallGraph),function(name) name %in% c("envir")), names(formals(pipeExprs))), function(argName) append(priorCallGraph[[argName]], list(...)[[argName]]))
    #args <- mergeLists(priorCallGraph$args, list(...)), names(formals(pipeExprs)))
    #args <- mergeLists(priorCallGraph, list(...)), names(formals(pipeExprs)))
    #args <- append(mget(intersect(discard(names(priorCallGraph),function(name) name %in% c("envir")), names(formals(pipeExprs))), priorCallGraph), list(...))
    #debug_message(paste0(show(args)))
    #show(args)
    #g <- do.call(f, args)

    #partialPipeExprs <- partial(pipeExprs, ... = , priorCallGraph=priorCallGraph) # envir is now parent. I think it's okay to reuse this since we are not modifying it.
    #g <- tryCatch(do.call(partialPipeExprs, args), error = function(e) show(e))
    g <- do.call(pipeExprs, args)
    #debug_message(paste0("callGraph id after repipe:", g$id,"\n"))
    #pipeExprs(g, exprs, processors$pipe$pre=processors$pipe$pre, processors$pipe$post=g$processors$pipe$post, processors$vertex$pre=g$processors$vertex$pre, processors$vertex$post=g$processors$vertex$post, reactive=g$reactive, priorCallGraph=priorCallGraph)
    #do.call(pipeExprs, append(list(g=g, exprs=exprs), g)
}
as.graph <- function(callGraph) {
    library(graph)
    g <- new("graphNEL", nodes=names(callGraph$vertices), edgemode="directed")
    for (edge in callGraph$edges) {
        #g <- addEdge(edge[[1]]$name, edge[[2]]$name, g, 1)
        g <- addEdge(edge[[1]], edge[[2]], g, 1)
    }
    #g@graphData$attrs = callGraph$attrs
    g
}

write.dot <- function(g, path=file.path(dir,paste0(g$id,".dot")), dir=tempdir()) {
    defaultAttrs <- list(node=list(href="#",cacheKey="",style="filled",fillcolor="transparent"))
    #nAttrs <- list()
    nAttrs <- Reduce(function(nAttrs, attr) { nAttrs[[attr]] <- lapply(Filter(function(v) !is.null(v[[attr]]), g$vertices), function(v) v[[attr]]); nAttrs }, names(defaultAttrs$node), list())
    #nAttrs <- Reduce(function(nAttrs, attr) { nAttrs[[attr]] <- lapply(g$vertices, function(v) v[[attr]]); nAttrs }, names(g$attrs$node), list())
#    debug_message(paste0("Names: "))
#    lapply(names(nAttrs), cat)
#    debug_message(paste0("Values: "))
#    lapply(nAttrs, cat)
    #nAttrs$cacheKey <- lapply(g$vertices, function(v) v$cacheKey)
#    nAttrs$href <- lapply(g$vertices, function(v) {
#        if (!is.null(v$href)) {
#            v$href
#        #} else if (!is.null(v$reprFile)) {
#        #    paste0("?file=",v$reprFile)
#        } else {
#            "#"
#        }
#    })
    #browser();
    toDot(as.graph(g), path, nodeAttrs=nAttrs, attrs=defaultAttrs)
    #debug_message(paste0(paste0("Wrote call graph to path ", path,"\n")))
    path
}

# Visualize with: https://github.com/magjac/d3-graphviz
#source("callGraph.R")
#library("digest")
#library("sets")
#setwd("/home/cld/code/R/")
#dotPath <- "/home/cld/virginia.js/static/hs.dot"
#g <- pipe("hsWords.R")
#plot(g, nodeAttrs=nAttrs)
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
            #a <- sapply(Filter(function(edge) edge[[1]] %in% below, g$edges), function(edge) edge[[2]])
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
        #g$edges <- append(g$edges, append(cartesianProduct(below, paste0(prefix,names(maximalVertices(h)))), cartesianProduct(paste0(prefix,names(minimalVertices(h))), above)))
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
