import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedWriter;
import java.io.File;
import java.util.Vector;
import java.util.Deque;
import java.util.ArrayDeque;
import java.util.Iterator;
class Process
{
    int id;
    int prev_pt;
    int lastsendorrecorlocevntpt;//variable to check if multiple events -msg send/rcv or local event happened at the same instant --used to update prev(Old) pt,l,c only when the first event occurs at a specific physical time

    Clock clock=new Clock();
    Clock prev_clock=new Clock();
    //queue to remember interval-candidates
    Deque<Candidate> candQueue;
    //queue to remember values corresponding to message sends
    Deque<MessageSendStruct> log;
    int msg_counter;
    Deque<ChangePoint> cPointQueue;
    Deque<ChangePoint> cPointQueueNextBatch;
    //variable to help ignore true intervals at a specific frequency
    int acceptInterval;	
    int lastAcceptedStartPt;
    int lastIgnoredStartPt;
    int ignoredMsgCnt;
    Process(int unique_id, Clock nwclock)
    {
        id=unique_id;
        clock=nwclock;

        msg_counter=0;
        if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
        {
            Vector<Integer> hlcvector=new Vector<Integer>();
            hlcvector.add(0);
            hlcvector.add(0);
            hlcvector.add(0);
            prev_clock= new HLC(hlcvector);
        }
        prev_pt=0;
        log = new ArrayDeque<MessageSendStruct>();
        candQueue= new ArrayDeque<Candidate>();
        cPointQueue= new ArrayDeque<ChangePoint>();
        cPointQueueNextBatch= new ArrayDeque<ChangePoint>();
        lastsendorrecorlocevntpt=-1;
		acceptInterval=0;
        lastAcceptedStartPt=0;
        lastIgnoredStartPt=0;
        ignoredMsgCnt=0;
    }

    void setId(int passed_id){id=passed_id;}
    void setProcClock(Clock nwclock){clock.setClock(nwclock.getClock());}
    void setProcOldClock(Clock passed_clock){prev_clock.setClock(passed_clock.getClock());}
    void setlastsendorrecorlocevntpt(int sendreclocventpt){lastsendorrecorlocevntpt=sendreclocventpt;}
    void setAcceptInterval(int value){acceptInterval=value;}
	void setLastAcceptedStartPt(int startPt){lastAcceptedStartPt=startPt;}
    void setLastIgnoredStartPt(int startPt){lastIgnoredStartPt=startPt;}	
    void setIgnoredMsgCnt(int cnt){ignoredMsgCnt=cnt;}
    int getIgnoredMsgCnt(){return ignoredMsgCnt;}
    int getLastIgnoredStartPt(){return lastIgnoredStartPt;}
    int getLastAcceptedStartPt(){return lastAcceptedStartPt;}
    int getAcceptInterval(){return acceptInterval;}
    int getId(){return id;}
    Clock getProcClock(){return clock;}
    Clock getProcOldClock(){return prev_clock;}
    int getlastsendorrecorlocevntpt(){return lastsendorrecorlocevntpt;}
    Deque<Candidate> getCandQueue()
    {
        return candQueue;
    }
    void setCandQueue(Deque<Candidate> updatedQueue)
    {
        candQueue=updatedQueue;
    }
    Deque<ChangePoint> getCPtQueue()
    {
        return cPointQueue;
    }
    Deque<ChangePoint> getCPtQueueNextBatch()
    {
        return cPointQueueNextBatch;
    }
    void deepCopyCurrentCPtQueue(Deque<ChangePoint> updatedQueue){
        cPointQueue= new ArrayDeque<ChangePoint>();
        while(!updatedQueue.isEmpty()) {
            cPointQueue.add(updatedQueue.removeFirst());
        }
    }
    void setCPtQueue(Deque<ChangePoint> updatedQueue) {
        cPointQueue=updatedQueue;
    }
    //clear queue method at a process - given time x --CLEARQUEUE
    Candidate clearQueueTill(Clock tillend)
    {
        //System.out.println("clear queue at process"+id+"tillendl"+tillendl+"tillendc"+tillendc);
        while(!(candQueue.isEmpty()) &&(((candQueue.peekFirst()).getEndClock().lessThan(tillend)) || ((candQueue.peekFirst()).getEndClock().equalTo(tillend))))
        {
            //pop all candidates with start time smaller than x
            candQueue.removeFirst();
        }
        //set the front candidate in my queue as my representative in Token--will be done at the method that called this method
        return candQueue.peekFirst();
    }
    Candidate newCandidateOccurance(Clock intervalstart, Clock intervalend)
    {
        Candidate newCand= new Candidate(intervalstart, intervalend);
        candQueue.add(newCand);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter candbw2= new BufferedWriter(new FileWriter("Candidates"+id+".txt", true));//true for append
                candbw2.append("<"+intervalstart.getClock()+"> to <"+intervalend.getClock()+">\n");
                candbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
        return newCand;
    }
    //0- add to process' current batch's changepoint queue
    //1- add to process' next batch's changepoint queue
    //2- add to process' both batchs' changepoint queue
    void newChangePoint(Clock cPtTime, int endPtIdentifier, int value)
    {
        ChangePoint newCPt= new ChangePoint(cPtTime, endPtIdentifier, value);
        cPointQueue.add(newCPt);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter cptbw2= new BufferedWriter(new FileWriter("ChangePoints"+id+".txt", true));//true for append
                cptbw2.append("<"+cPtTime.getClock()+", type: "+endPtIdentifier+", value"+value+">\n");
                cptbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
    }
    void updateClockLocalOrSendMsg(int physicalTime, boolean sendmsg)
    {
        if(lastsendorrecorlocevntpt!=physicalTime)//if a message send/receive did not happen at the same instant update old pt - otherwise don't because old pt is required for interval reporting
        {//pt is also same-still update old_value
            setProcOldClock(getProcClock());
        }
        clock.updateLocal(physicalTime);
        //System.out.println("At Process:"+id+"; Physical Time:"+physicalTime);
        if(sendmsg)
        {
            Clock formsgclk=new Clock();
            //push message id, l, c into queue
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
            {
                Vector<Integer> hlcvector=new Vector<Integer>();
                hlcvector.add(0);
                hlcvector.add(0);
                hlcvector.add(0);
                formsgclk=new HLC(hlcvector);
            }
            formsgclk.setClock(clock.getClock());//copying clock values to new clk object for msg timestamping
            MessageSendStruct newmsg= new MessageSendStruct(msg_counter++,formsgclk);
            log.add(newmsg);
        }

        setlastsendorrecorlocevntpt(physicalTime);
    }
    void updateClockMessageRceive(int receiver_time, Clock sndrClk)
    {
        if(getlastsendorrecorlocevntpt()!=receiver_time)
        {
            setProcOldClock(getProcClock());
        }
        clock.updateMsgRcv(receiver_time,sndrClk);
        setlastsendorrecorlocevntpt(receiver_time);
    }
    MessageSendStruct getClockfromQueue(int passed_phytime)
    {
        while(log.peek().getMsgClock().getClock().get(0)!=passed_phytime)
        {
            //System.out.println(passed_phytime+","+log.peek().getPt());
            System.out.println("FIFO VIOLATED...popping..");
            log.removeFirst();
        }
        MessageSendStruct msgptclk=log.peek();
        if(msgptclk!=null)
        {
            if(passed_phytime == msgptclk.getMsgClock().getClock().get(0))
            {
                //System.out.println("FOUND MATCHING SEND");
                return log.removeFirst();
            }
            else
            {
                System.out.println("CODE THAT SHOULD NOT EXECUTE");
                System.exit(0);
            }
            return log.peek();
        }
        else
        {
            System.out.println("SEND QUEUE EMPTY");
            System.exit(0);
            return msgptclk;
        }
    }

    void printCandQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in write mode so anything already existing will be cleared
            }

            if (!candQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (Candidate cand : candQueue)
                {
                    bw_deb1.write("<"+cand.getStartClock().getClock().get(1)+","+cand.getStartClock().getClock().get(2)+">-<" + cand.getEndClock().getClock().get(1)+","+ cand.getEndClock().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }
    void printCPtQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in append mode so anything already existing will not be cleared
            }
            if (!cPointQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (ChangePoint cPt : cPointQueue)
                {
                    bw_deb1.write(cPt.getcPointTimestamp().getClock().get(0) +", <" + cPt.getcPointTimestamp().getClock().get(1)+"," + cPt.getcPointTimestamp().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }
    void fixLastChangepoint(HLC largestIntervalEnd){
        if(!cPointQueue.isEmpty()){
            //get last two changepoints - first, second
            ChangePoint second = cPointQueue.removeLast();
            ChangePoint first = cPointQueue.removeLast();
            while(largestIntervalEnd.lessThan(second.getcPointTimestamp())){
                //if first is larger than largestIntervalEnd
                if (largestIntervalEnd.lessThan(first.getcPointTimestamp())) {
                    //drop first and second
                    //continue loop
                    second = cPointQueue.removeLast();
                    first = cPointQueue.removeLast();
                } else if (largestIntervalEnd.lessThan(second.getcPointTimestamp())) {
                    //if first is not larger but second is larger than largestIntervalEnd
                    //update second's clock to largestIntervalEnd
                    second.setcPointTimestamp(largestIntervalEnd);
                    //end loop - because the intervals are cleaned before invoking this function all changepoints before a have smaller timestamps
                }
            }
            //put it back into the queue
            cPointQueue.add(first);
            cPointQueue.add(second);
        }
    }
    void clearCurrentChangePointQ(){
        cPointQueue.clear();
    }
    void clearNextChangePointQ(){
        cPointQueueNextBatch.clear();
    }
    void fillNextQueueFromCurrentQueue(int batchBorderPt){
        // Returns an iterator over the elements in this deque
        Iterator<ChangePoint> it = cPointQueue.iterator();
        while (it.hasNext()) {
            ChangePoint currLCpt= it.next();
            ChangePoint currRCpt= it.next();
            //any pair of changepoint with right changepoint-ohysical-timestamp greater than current window's strict right should be copied
            if(currRCpt.getcPointTimestamp().getClock().elementAt(0)>=batchBorderPt) {
                ChangePoint cptLCopy = new ChangePoint(new HLC(currLCpt.getcPointTimestamp().getClock()), currLCpt.getEndPointType(), currLCpt.getiValue());
                ChangePoint cptRCopy = new ChangePoint(new HLC(currRCpt.getcPointTimestamp().getClock()), currRCpt.getEndPointType(), currRCpt.getiValue());
                cPointQueueNextBatch.add(cptLCopy);
                cPointQueueNextBatch.add(cptRCopy);
            }
        }
    }
    Deque<ChangePoint> cleanUpChangePtQ(){
        Deque<ChangePoint> cleansedQ = new ArrayDeque<ChangePoint>();
        Deque<ChangePoint> intermediateCPtsQ = new ArrayDeque<ChangePoint>();
        ChangePoint currentLCPt=null, currentRCPt=null;
        if(!cPointQueue.isEmpty()){
            currentLCPt=getCPtQueue().removeFirst(); //Lj
            currentRCPt=getCPtQueue().removeFirst(); //Rj;
        }
        //until the changepoints queue and intermediate changepoints queue is processed
        while (cPointQueue.peek() != null || intermediateCPtsQ.peek()!=null) {
            //if changepoints queue is empty but intermediate changepoints queue still has some changepoints
            if(cPointQueue.peek()==null && intermediateCPtsQ.peek()!=null){
                //move all changepoints from the intermediate queue to cPointQueue
                while (intermediateCPtsQ.peek() != null){
                    ChangePoint interCpt=intermediateCPtsQ.removeFirst();
                    cPointQueue.add(interCpt);
                }
                intermediateCPtsQ.clear();//clear intermediate queue
                continue;//continue processing cPointQueue
            }
            ChangePoint nextLCPt = getCPtQueue().removeFirst(); //Li
            ChangePoint nextRCPt = getCPtQueue().removeFirst(); //Ri
            //no overlap
            if (currentRCPt.getcPointTimestamp().lessThan(nextLCPt.getcPointTimestamp()) || currentRCPt.getcPointTimestamp().equalTo(nextLCPt.getcPointTimestamp())) {
                //clean up
                //put current interval
                cleansedQ.add(currentLCPt);
                cleansedQ.add(currentRCPt);
                //put back the non overlapping next-interval changepoints
                cPointQueue.addFirst(nextRCPt);
                cPointQueue.addFirst(nextLCPt);
                //insert all intermediate changepoints back into the cPointQueue
                while (intermediateCPtsQ.peek() != null) {//process any intermediate changepoints
                    ChangePoint intermediateCPtR = intermediateCPtsQ.removeLast();
                    ChangePoint intermediateCPtL = intermediateCPtsQ.removeLast();
                    //currentCPt overlapped with entire intermediate interval drop it else modify its left end
                    if (intermediateCPtR.getcPointTimestamp().lessThan(currentRCPt.getcPointTimestamp()) || intermediateCPtR.getcPointTimestamp().equalTo(currentRCPt.getcPointTimestamp())) {
                        //should not happen because the right endpoint of the intermediate intervals are also extended by epsilon
                        // so should be larger
                        System.out.println("At P" + getId() + ", gamma " + TraceHLCTimestampingOfflineArithPredDet.gamma + ",  Intermediate interval has right endpoint" + intermediateCPtR.getcPointTimestamp().getClock().toString() + " smaller than the current interval's right endpoint" + currentRCPt.getcPointTimestamp().getClock().toString() + ".");
                        System.exit(0);
                        continue;//ignore any intermediate intervals with smaller value
                    }
                    cPointQueue.addFirst(intermediateCPtR);
                    cPointQueue.addFirst(intermediateCPtL);
                }
                //remove first two changepoints and make them the current changepoints
                currentLCPt=getCPtQueue().removeFirst(); //Lj
                currentRCPt=getCPtQueue().removeFirst(); //Rj;
            } else if (nextLCPt.getiValue() > currentLCPt.getiValue()) {//there is overlap and the successive overlapping interval has higher value
                //discard intermediateCPtsQ
                intermediateCPtsQ.clear();
                //set Rj's timestamp to Li's timestamp
                Clock nextLClock = nextLCPt.getcPointTimestamp();
                Clock origRTime = currentRCPt.getcPointTimestamp();
                origRTime.setClock(nextLClock.getClock());
                currentRCPt.setcPointTimestamp(origRTime);
                if (!currentRCPt.getcPointTimestamp().lessThan(currentLCPt.getcPointTimestamp())) {
                    cleansedQ.add(currentLCPt);
                    cleansedQ.add(currentRCPt);
                }
                currentLCPt = nextLCPt;
                currentRCPt = nextRCPt;
            } else {//there is overlap and the successive overlapping interval has smaller or equal value
                //set Li's timestamp to Rj's timestamp
                Clock currRClock = currentRCPt.getcPointTimestamp();
                Clock origLTime = nextLCPt.getcPointTimestamp();
                origLTime.setClock(currRClock.getClock());
                nextLCPt.setcPointTimestamp(origLTime);
                if(nextLCPt.getcPointTimestamp().equalTo(nextRCPt.getcPointTimestamp())){
                    continue;//ignore the next interval because they ended having equal starting and ending points after update
                }
                if (!nextLCPt.getcPointTimestamp().lessThan(nextRCPt.getcPointTimestamp())) {//should not execute- added for debugging purposes
                    System.out.println("Updated next interval has larger left endpoint " + nextLCPt.getcPointTimestamp().getClock().toString() + "than right endpoint" + nextRCPt.getcPointTimestamp().getClock().toString() + ".");
                    System.exit(0);
                }
                intermediateCPtsQ.add(nextLCPt);
                intermediateCPtsQ.add(nextRCPt);
                //currentLCPt and currentRCPt stay the same
            }//end of else
        }//end of while(cPointQueue.peek() != null)
        //add last two changepoints
        if(currentLCPt!=null){
            cleansedQ.add(currentLCPt);
        }
        if(currentRCPt!=null){
            cleansedQ.add(currentRCPt);
        }
        return cleansedQ;
    }
}