#!/bin/bash
# Used by render.com to get the artifact
#
# Usage:
# GITHUB_AUTH_TOKEN=ghp_BLAHBLAHBLAH wiki/get-artifact GIT_SHA

# Exit on error
set -e

URL='https://api.github.com/repos/standardml/twelf/actions/artifacts?per_page=100&name=wiki-ssg'

while true
do
    ARTIFACT_ACCESS_URL=$(\
        curl -L \
          -H "Accept: application/vnd.github+json" \
          -H "Authorization: Bearer $GITHUB_AUTH_TOKEN" \
          -H "X-GitHub-Api-Version: 2022-11-28" \
        $URL 2> /dev/null | jq -r '                                                                        
          [ .artifacts[]  
            | if .workflow_run.head_sha == "'$1'"
              then .archive_download_url else ""
              end
          ] as $urls
          | $urls | paths(. != "")[0]
          | $urls[.]'\
          )
    if [ -z $ARTIFACT_ACCESS_URL ]
    then
        echo "No SSG artifact found for commit $1"
        echo "Pausing."
        sleep 10
    else
        break
    fi
done

rm -rf dist
mkdir dist
curl -o dist/wiki.zip -L \
  -H "Authorization: Bearer $GITHUB_AUTH_TOKEN" \
  $ARTIFACT_ACCESS_URL 2> /dev/null

cd dist
unzip wiki.zip