"""Idiomatic Starlette responses; Uvicorn selects uvloop/httptools explicitly."""
import asyncio
import json
from starlette.applications import Starlette
from starlette.responses import JSONResponse, PlainTextResponse, Response
from starlette.routing import Route

async def text(request):
    return PlainTextResponse("Hello, World!")

async def json_response(request):
    return JSONResponse({"message": "Hello, World!"})

async def json_static(request):
    return Response(b'{"message":"Hello, World!"}', media_type="application/json")

def records():
    return [{"id": i, "message": f"record {i}"} for i in range(20)]

RECORDS_JSON = json.dumps(records(), separators=(",", ":")).encode()

async def stage_static(request):
    return Response(RECORDS_JSON, media_type="application/json")

async def stage_sleep(request):
    await asyncio.sleep(0.001)
    return Response(RECORDS_JSON, media_type="application/json")

async def stage_encode(request):
    return JSONResponse(records())

async def app_response(request):
    await asyncio.sleep(0.001)
    return JSONResponse(records())

app = Starlette(routes=[
    Route("/text", text), Route("/json", json_response),
    Route("/json-static", json_static),
    Route("/stage/static", stage_static), Route("/stage/sleep", stage_sleep),
    Route("/stage/encode", stage_encode), Route("/app", app_response),
])
